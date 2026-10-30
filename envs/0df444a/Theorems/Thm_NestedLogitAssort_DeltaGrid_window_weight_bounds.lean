-- Prove2me | Theorems.Thm_NestedLogitAssort_DeltaGrid_window_weight_bounds
-- name    : NestedLogitAssort.DeltaGrid.window_weight_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:11:25.385557+00:00
-- url     : https://prove2.me/theorems/7c7d8053-fb77-403b-8fb6-99486b982fe7
-- title:
--   Proof of Theorem 12: bounds on $(\delta^l)^{\gamma_i-1}$ and $(\delta^{l-1})^{\gamma_i}$ through $V_i(S_i)$
-- statement:
--   Let $\delta>1$, $\gamma\ge0$, $l\in\mathbb Z$, and let $W$ be a real number in the window $\delta^{l-1}\le W\le\delta^l$. Then
--
--   $$
--   (\delta^l)^{\gamma-1}\ge\delta^{-[1-\gamma]^+}\,W^{\gamma-1}\qquad\text{and}\qquad(\delta^{l-1})^{\gamma}\le W^{\gamma},
--   $$
--
--   where $[a]^+=\max\{a,0\}$. In the proof of Theorem 12 this is applied to $W=V_i(S_i)$ and $\gamma=\gamma_i$, to replace the powers of $\delta^l$ in (36) by powers of $V_i(S_i)$.
--
--   Differences from the source:
--   - generalization: the bounds are stated for W = V_i(S_i) → any real W with δ^(l−1) ≤ W ≤ δ^l; reason: V_i(S_i) lies in this window by the choice of l; the statement specializes to the page
--   - encoding: δ^l, δ^(l−1) for l ∈ Z and the factors δ^(2γ̄+1), δ^(γ̄+1), δ^(−[a]^+) → zpow for the integer powers, Real.rpow for the real exponents, [a]^+ as max a 0; reason: Lean convention; same values
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 54

import Mathlib

namespace NestedLogitAssort.DeltaGrid

/-- **Bounds on `(δ^l)^{γ_i − 1}` and `(δ^{l−1})^{γ_i}` through `V_i(S_i)`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 54 (unnumbered): from
`δ^{l−1} ≤ V_i(S_i) ≤ δ^l`, `(δ^l)^{γ_i−1} ≥ δ^{−[1−γ_i]^+} V_i(S_i)^{γ_i−1}` and
`(δ^{l−1})^{γ_i} ≤ V_i(S_i)^{γ_i}`.

Stated for every real `W` in the window `[δ^{l−1}, δ^l]`; the page applies it to `W = V_i(S_i)`.

**Formalization Note.** `δ ^ l` and `δ ^ (l - 1)` are `zpow`; the other powers are `Real.rpow`.
`W ≥ δ^{l−1} > 0`. -/
theorem window_weight_bounds (δ : ℝ) (hδ : 1 < δ) (γ : ℝ) (hγ : 0 ≤ γ) (l : ℤ) (W : ℝ)
    (hW1 : δ ^ (l - 1) ≤ W) (hW2 : W ≤ δ ^ l) :
    δ ^ (-(max (1 - γ) 0)) * W ^ (γ - 1) ≤ (δ ^ l) ^ (γ - 1) ∧
      (δ ^ (l - 1)) ^ γ ≤ W ^ γ := by sorry

end NestedLogitAssort.DeltaGrid
