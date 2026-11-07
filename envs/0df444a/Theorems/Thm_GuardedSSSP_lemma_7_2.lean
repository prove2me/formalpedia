-- Prove2me | Theorems.Thm_GuardedSSSP_lemma_7_2
-- name    : GuardedSSSP.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:47:46.070184+00:00
-- url     : https://prove2.me/theorems/6172f615-50d5-462e-8fc6-84625a66498c
-- title:
--   Lemma 7.2 — exponent mass one, convergence of $\Phi$, identities (22)–(24), and (25)
-- statement:
--   For real $x\ge0$:
--
--   1. $\sum_{i=1}^{d}2^{-i}+2\cdot2^{-(d+1)}=1$ for every $d\ge0$ (the exponents of $f_d$ have mass one);
--   2. the partial products $\prod_{i=1}^{N}L_i(x)^{2^{-i}}$ converge to $\Phi(x)$ as $N\to\infty$, and $\Phi(x)>0$;
--   3. for every $d\ge0$,
--   $$f_{d+1}(x)^2=L_1(x)f_d(L_1(x)+2),\qquad \frac{f_{d+1}(x)}{f_d(x)}=\Big(\frac{L_{d+3}(x)}{L_{d+2}(x)}\Big)^{2^{-(d+2)}};$$
--   4. $\Phi(x)^2=L_1(x)\Phi(L_1(x)+2)$;
--   5. if the iterates decrease ($L_{i+1}(x)\le L_i(x)$ for all $i\ge1$), then for every $d$
--   $$\sqrt{L_1(x)}\le\Phi(x)\le f_d(x)\le L_1(x);$$
--   6. $f_d(x)\to\Phi(x)$ as $d\to\infty$.
--
--   These identities drive the generation recurrence and the comparison of the finite factors $f_d$ with the envelope $\Phi$.
--
--   Differences from the source:
--   - generalization: (22), (23) for all d ≥ 1 → for all d ≥ 0; reason: f₀ is defined by (10) and the identities hold at d = 0; specializes to d ≥ 1
--   - encoding: on the decreasing-iterate region → hypothesis L_{i+1}(x) ≤ L_i(x) for all i ≥ 1; reason: the region is defined by that property (§7)
--   - encoding: the product defining Φ converges to a finite positive value → the partial products tend to Phi x, and 0 < Phi x, with Phi defined as exp of the series of logarithms; reason: Phi avoids a tprod junk value; the convergence clause carries the content
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Lemma 7.2, pp.14–15 (PDF pp.15–16)

import Mathlib
import Definitions.Def_GuardedSSSP_LogHierarchy

namespace GuardedSSSP

open Filter Topology

/-- **Lemma 7.2** (Mass, convergence, and identities), pp.14–15 (PDF pp.15–16).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "The exponents in each f_d have total mass one. The product
defining Φ converges to a finite positive value. For all d ≥ 1, f_{d+1}(x)² = L₁(x) f_d(L₁(x) + 2), (22)
f_{d+1}(x)/f_d(x) = (L_{d+3}(x)/L_{d+2}(x))^{2^{−(d+2)}}, (23) Φ(x)² = L₁(x)Φ(L₁(x) + 2). (24) On the
decreasing-iterate region, √L₁(x) ≤ Φ(x) ≤ f_d(x) ≤ L₁(x). (25) For each fixed x, f_d(x) → Φ(x) as d → ∞."

Clauses, for real `x ≥ 0` (the domain of (9)–(11), §7):
1. `∑_{i=1}^{d} 2^{−i} + 2·2^{−(d+1)} = 1` for every `d`;
2. the partial products `∏_{i=1}^{N} L_i(x)^{2^{−i}}` converge to `Φ(x)`, and `Φ(x) > 0`;
3. (22) and (23) for every `d ≥ 0`;
4. (24);
5. (25) for every `d`, at every `x` whose iterates decrease (`L_{i+1}(x) ≤ L_i(x)` for all `i ≥ 1`);
6. `f_d(x) → Φ(x)` as `d → ∞`.

**Formalization Note.** The decreasing-iterate region is written as the hypothesis that the iterates
decrease. (22) and (23) are stated for `d ≥ 0`, which contains the paper's `d ≥ 1`. -/
theorem lemma_7_2 :
    (∀ d : ℕ, (∑ i ∈ Finset.Icc 1 d, (2 : ℝ) ^ (-(i : ℝ))) + 2 * (2 : ℝ) ^ (-((d : ℝ) + 1)) = 1) ∧
    (∀ x : ℝ, 0 ≤ x →
      Tendsto (fun N : ℕ => ∏ i ∈ Finset.Icc 1 N, L i x ^ ((2 : ℝ) ^ (-(i : ℝ)))) atTop
        (𝓝 (Phi x)) ∧ 0 < Phi x) ∧
    (∀ (d : ℕ) (x : ℝ), 0 ≤ x → f (d + 1) x ^ 2 = L 1 x * f d (L 1 x + 2)) ∧
    (∀ (d : ℕ) (x : ℝ), 0 ≤ x →
      f (d + 1) x / f d x = (L (d + 3) x / L (d + 2) x) ^ ((2 : ℝ) ^ (-((d : ℝ) + 2)))) ∧
    (∀ x : ℝ, 0 ≤ x → Phi x ^ 2 = L 1 x * Phi (L 1 x + 2)) ∧
    (∀ x : ℝ, 0 ≤ x → (∀ i : ℕ, 1 ≤ i → L (i + 1) x ≤ L i x) → ∀ d : ℕ,
      Real.sqrt (L 1 x) ≤ Phi x ∧ Phi x ≤ f d x ∧ f d x ≤ L 1 x) ∧
    (∀ x : ℝ, 0 ≤ x → Tendsto (fun d : ℕ => f d x) atTop (𝓝 (Phi x))) := by sorry

end GuardedSSSP
