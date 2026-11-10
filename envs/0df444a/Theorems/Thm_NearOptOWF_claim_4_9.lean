-- Prove2me | Theorems.Thm_NearOptOWF_claim_4_9
-- name    : NearOptOWF.claim_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:14:27.725419+00:00
-- url     : https://prove2.me/theorems/d6103c41-2934-42b5-b1f3-e44e4cbf7eed
-- title:
--   Claim 4.9 — satisfiable $\varphi$: $\Pr_{G,y}[E] \le 2^{n^{2\delta}-m}/2$
-- statement:
--   With the objects of Claim 4.8, let $\varphi$ be **satisfiable**, and assume that for all $k, y$ the distribution of $A(P_{k,y}, y)$ is at most $\eta$-far from the ideal distribution, which outputs $\perp$ with probability $\Pr[A(P_{k,y}, y) = \perp]$ and otherwise a uniform pre-image from $G_{\varphi,y}^{-1}(y)$. Then, for $x \leftarrow A(G_{\varphi,y}, y)$ and $E = E_1 \wedge E_2$:
--
--   1. $\Pr_{G,y}[E] \le 2^{r - m} + \eta$;
--   2. if $r = \lceil n^\delta \rceil$ and $\eta \le 2^{n^{2\delta} - m}/2 - 2^{r-m}$, then
--   $$
--   \Pr_{G,y}[E] \le \frac{2^{n^{2\delta} - m}}{2}.
--   $$
--
--   The first bound is the proof's $2^{n^\delta - N} \cdot 2^{N-m} + 2^N \cdot 2^{-\lambda^{\Omega(1)}}$; the second is the printed claim "for sufficiently large polynomial $\lambda$".
--
--   Differences from the source:
--   - generalization: the sampler A of Claim 4.7, the puncturable PRF G, and the error 2^N·2^{-λ^{Ω(1)}} → any output distributions D(g, y), any key-indexed circuits G_k, any circuits P k y computing G_{φ,y}, and a uniformity hypothesis with error η on P k y; reason: the proof uses only uniformity on pre-images; the printed claim is the instance η = 2^N·2^{-λ^c}
--   - generalization: φ with n^δ input bits → φ with any r ≤ N input bits (first conclusion) and r = ⌈n^δ⌉ for any n and any real δ (second conclusion); reason: n^δ is not an integer; δ > 0 is not needed since the second conclusion follows from the first
--   - reading: "for sufficiently large polynomial λ, Pr[E] ≤ 2^{n^{2δ}−m}/2" → explicit hypothesis η ≤ 2^{n^{2δ}−m}/2 − 2^{r−m}; reason: this is exactly what "sufficiently large λ" provides in the proof
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Claim 4.9, p.16 (PDF p.18), with the bound of its proof, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_LaconicBarrier_coinAvg
import Definitions.Def_HybridXorLift_tvDist
import Definitions.Def_NearOptOWF_idealDist

namespace NearOptOWF

open LaconicBarrier

/-- **Claim 4.9** (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Claim 4.9, p.16 (PDF p.18), with the bound of its proof, p.17 (PDF p.19)),
in the generality its proof uses: with the objects of Claim 4.8, let `φ` be **satisfiable**, and assume
that for all `k, y` the distribution `A(G_{φ,y}, y)` is `η`-far from the ideal one (`⊥` with
probability `Pr[A(G_{φ,y}, y) = ⊥]`, otherwise a uniform pre-image from `G_{φ,y}⁻¹(y)`). Then for
`x ← A(G_{φ,y}, y)`:

1. `Pr_{G,y}[E] ≤ 2^{r−m} + η` (the proof's `2^{n^δ−N} · 2^{N−m} + 2^N · 2^{−λ^{Ω(1)}}`);
2. the printed form: if `r = ⌈n^δ⌉` and `η ≤ 2^{n^{2δ}−m}/2 − 2^{r−m}` ("for sufficiently large
   polynomial `λ`"), then `Pr_{G,y}[E] ≤ 2^{n^{2δ}−m}/2`.

**Formalization Note** `φ` has `r` inputs in place of `n^δ` (not an integer); the instance of the proof
of Theorem 4.1 is `r = ⌈n^δ⌉`. The statistical error is the explicit parameter `η`. -/
theorem claim_4_9 (N m r a : ℕ) (hr : r ≤ N) (φ : KarpLiptonOM.Circuit r)
    (hφ : ∃ u : Fin r → Bool, φ.eval (List.ofFn u) = true)
    (Gs : (Fin a → Bool) → MCircuit N) (P : (Fin a → Bool) → (Fin m → Bool) → MCircuit N)
    (hP : ∀ (k : Fin a → Bool) (y : Fin m → Bool) (x : Fin N → Bool),
      (P k y).eval (List.ofFn x) =
        if φ.eval ((List.ofFn x).take r) = true then List.ofFn y else (Gs k).eval (List.ofFn x))
    (D : MCircuit N → List Bool → Option (Fin N → Bool) → ℝ)
    (hD0 : ∀ g y o, 0 ≤ D g y o) (hD1 : ∀ g y, ∑ o, D g y o = 1)
    (η : ℝ)
    (hη : ∀ k y, HybridXorLift.tvDist (D (P k y) (List.ofFn y))
      (idealDist (P k y) (List.ofFn y) (D (P k y) (List.ofFn y) none)) ≤ η) :
    (coinAvg a fun k => coinAvg m fun y => ∑ z : Fin N → Bool,
      if (P k y).eval (List.ofFn z) = List.ofFn y ∧ φ.eval ((List.ofFn z).take r) = false then
        D (P k y) (List.ofFn y) (some z) else 0) ≤ (2 : ℝ) ^ ((r : ℝ) - m) + η ∧
    ∀ (n : ℕ) (δ : ℝ), r = ⌈(n : ℝ) ^ δ⌉₊ →
      η ≤ (2 : ℝ) ^ ((n : ℝ) ^ (2 * δ) - m) / 2 - (2 : ℝ) ^ ((r : ℝ) - m) →
      (coinAvg a fun k => coinAvg m fun y => ∑ z : Fin N → Bool,
      if (P k y).eval (List.ofFn z) = List.ofFn y ∧ φ.eval ((List.ofFn z).take r) = false then
        D (P k y) (List.ofFn y) (some z) else 0) ≤ (2 : ℝ) ^ ((n : ℝ) ^ (2 * δ) - m) / 2 := by sorry

end NearOptOWF
