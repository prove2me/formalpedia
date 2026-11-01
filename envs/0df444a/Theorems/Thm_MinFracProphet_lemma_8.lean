-- Prove2me | Theorems.Thm_MinFracProphet_lemma_8
-- name    : MinFracProphet.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:22.92342+00:00
-- url     : https://prove2.me/theorems/d8eb3114-5fef-4a50-af12-0dfe03e71caa
-- title:
--   Lemma 8: $J_i(s)=b_i(1-s)^p$ and the optimal allocation (26) (corrected: exponent $1/(p-1)$ in (25))
-- statement:
--   Let $0<\ell\le u<\infty$, $p>1$ and $n\ge1$, and let the prices $C_1,\dots,C_n$ be independent, each with a distribution carried by $[\ell,u]$. Let $J_i$ be the cost-to-go functions (21), let $b_n(c)=c$ (24), and for $i<n$ let
--   $$
--   b_i(c)=\frac{c\,\mathbb E[b_{i+1}]}{\bigl(c^{1/(p-1)}+\mathbb E[b_{i+1}]^{1/(p-1)}\bigr)^{p-1}}.\tag{25}
--   $$
--   Then for every stage $i$, every state $s\in[0,1]$ and every price $c\in[\ell,u]$:
--
--   1. (23) $J_i(s,c)=b_i(c)\,(1-s)^p$;
--   2. (26) for $i<n$, the stage problem $\min_{0\le x\le1-s}\ c\,x^p+\mathbb E[J_{i+1}(s+x,C_{i+1})]$ has exactly one minimizer,
--   $$
--   x_i=\frac{\mathbb E[b_{i+1}]^{1/(p-1)}}{c^{1/(p-1)}+\mathbb E[b_{i+1}]^{1/(p-1)}}\,(1-s).
--   $$
--
--   So the dynamic program of Appendix B.1 is solved in closed form, by a scalar recursion on the means $\mathbb E[b_i]$.
--
--   **Formalization Note** Stages are 0-based in Lean. `dpB p ν i c` is $b_i(c)$ and `dpBeta p ν (i+1)` is $\mathbb E[b_{i+1}]$. The second clause is stated as equality of the set of minimizers over $[0,1-s]$ with the singleton $\{x_i\}$.
--
--   Differences from the source:
--   - correction: (25) with the exponent 1/p−1 on E[b_{i+1}] → exponent 1/(p−1); reason: the literal exponent makes the lemma false: n = 2, p = 2, C_1 ≡ 1, C_2 ≡ 4 satisfy every assumption, J_1(0) = min_x x² + 4(1−x)² = 4/5, while c E[b_2]/(c^{1/(p−1)} + E[b_2]^{1/p−1})^{p−1} = 4/(1 + 1/2) = 8/3; the proof’s last line but one and (26) use 1/(p−1)
--   - reading: (26) for i = 1,…,n → (26) for i < n; at the last stage x_n = 1 − s_n by (22); reason: E[b_{n+1}] is undefined
--   - generalization: the corresponding allocation is given by (26) → (26) is the unique minimizer of the stage problem; reason: uniqueness is added (the stage objective is strictly convex); it implies that (26) is an optimal allocation
--   - reading: an optimal algorithm has cost-to-go functions (23) → the cost-to-go functions (21) satisfy (23); reason: the cost-to-go of the optimal algorithm is (21), by the DP optimality milestone
--   - reading: D a distribution supported on [ℓ,u] (and the DP of Appendix B.1 for that problem) → independent laws ν_0,…,ν_{n−1}, each a probability measure with ν_i([ℓ,u]ᶜ) = 0, 0 < ℓ ≤ u; reason: “a distribution D” means the tuple D = (D_1,…,D_n) of §1.2; Lemma 8 and the lower bound use the DP only on such instances
--   - reading: (21): J_n(s_n) = c_n(1 − s_n), J_i(s_i) = min c_i(x_i) + E[J_{i+1}(s_i + x_i)] → J_{n−1}(s,c) = c(1−s)^p and J_i(s,c) = inf_{0≤y≤1−s} c y^p + E[J_{i+1}(s+y, C_{i+1})], a function of the state s and the realized price c; reason: c_i(·) is the cost function c_i x^p; the proof’s base case (p.22) reads J_n(s_n) = c_n(1 − s_n)^p
--   - encoding: stages i = 1,…,n → stages i = 0,…,n−1 (Lean stage i is the paper’s stage i+1), law ν ⟨i,_⟩; reason: Lean convention, a shift of the index
-- source:
--   Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, author manuscript (INFORMS template, sha256 672fa87c…79125d3), Lemma 8, (23)–(26), p.22 (exponent of (25) corrected)

import Mathlib
import Definitions.Def_MinFracProphet_DynamicProgram

open MeasureTheory

namespace MinFracProphet

/-- **Lemma 8**, p.22 of J. Qin, S. Vardi, A. Wierman, *Minimization Fractional Prophet
Inequalities for Sequential Procurement*, author manuscript (sha256 672fa87c…79125d3)
(corrected: exponent `1/(p-1)` in (25)).

Let `0 < ℓ ≤ u < ∞`, `p > 1`, `n ≥ 1`, and let the prices be independent with laws `ν_i` carried
by `[ℓ,u]`. For every stage `i`, every state `s ∈ [0,1]` and every price `c ∈ [ℓ,u]`:

1. (23) the cost-to-go is `J_i(s, c) = b_i(c) (1 - s)^p`, with `b_n(c) = c` (24) and
   `b_i(c) = c E[b_{i+1}] / (c^{1/(p-1)} + E[b_{i+1}]^{1/(p-1)})^{p-1}` (25);
2. (26) before the last stage, the stage problem `min_{0 ≤ x ≤ 1-s} c x^p + E[J_{i+1}(s + x)]` has
   the unique minimizer
   `x_i = E[b_{i+1}]^{1/(p-1)} (1 - s) / (c^{1/(p-1)} + E[b_{i+1}]^{1/(p-1)})`.

**Formalization Note** Stages are 0-based (Lean stage `i` is the paper's `i+1`; the last stage is
`n-1`). `dpB p ν i c` is `b_i(c)` and `dpBeta p ν (i+1)` is `E[b_{i+1}]`. The page prints the
exponent of `E[b_{i+1}]` in (25) as `1/p-1`, which is false (R10; counterexample `n = 2`, `p = 2`,
`C_1 ≡ 1`, `C_2 ≡ 4`: `J_1(0) = 4/5`, the literal formula gives `8/3`); the proof's last line but
one and (26) use `1/(p-1)`. (26) is printed for `i = 1, …, n`, but `E[b_{n+1}]` is undefined;
at the last stage `x_n = 1 - s_n` by (22) (R9). -/
theorem lemma_8 (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 1 < p) (ℓ u : ℝ) (hℓ : 0 < ℓ)
    (hℓu : ℓ ≤ u) (ν : Fin n → Measure ℝ) (hprob : ∀ i, IsProbabilityMeasure (ν i))
    (hsupp : ∀ i, ν i (Set.Icc ℓ u)ᶜ = 0) :
    ∀ i : ℕ, i < n → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ c ∈ Set.Icc ℓ u,
      costToGo p ν i s c = dpB p ν i c * (1 - s) ^ p ∧
      ∀ h : i + 1 < n,
        {y ∈ Set.Icc (0 : ℝ) (1 - s) | ∀ y' ∈ Set.Icc (0 : ℝ) (1 - s),
            c * y ^ p + ∫ c', costToGo p ν (i + 1) (s + y) c' ∂(ν ⟨i + 1, h⟩) ≤
              c * y' ^ p + ∫ c', costToGo p ν (i + 1) (s + y') c' ∂(ν ⟨i + 1, h⟩)} =
          {dpBeta p ν (i + 1) ^ (1 / (p - 1)) * (1 - s) /
            (c ^ (1 / (p - 1)) + dpBeta p ν (i + 1) ^ (1 / (p - 1)))} := by sorry

end MinFracProphet
