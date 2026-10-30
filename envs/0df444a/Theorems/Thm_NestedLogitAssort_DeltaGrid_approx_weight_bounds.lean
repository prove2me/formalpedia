-- Prove2me | Theorems.Thm_NestedLogitAssort_DeltaGrid_approx_weight_bounds
-- name    : NestedLogitAssort.DeltaGrid.approx_weight_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:10:21.252999+00:00
-- url     : https://prove2.me/theorems/f562df36-86a3-48be-95a8-94349fbfb4d9
-- title:
--   Proof of Theorem 12: bounds on $V_i(\hat S_{il})^{\gamma_i-1}$ and $V_i(\hat S_{il})^{\gamma_i}$
-- statement:
--   Let $\delta>1$, $\gamma\ge0$, $l\in\mathbb Z$, and let $W$ be a real number in the window $\delta^{l-1}\le W\le\delta^l$. Then
--
--   $$
--   W^{\gamma-1}\ge(\delta^l)^{\gamma-1}\,\delta^{-[\gamma-1]^+}\qquad\text{and}\qquad W^{\gamma}\le(\delta^l)^{\gamma},
--   $$
--
--   where $[a]^+=\max\{a,0\}$. In the proof of Theorem 12 this is applied to $W=V_i(\hat S_{il})$ and $\gamma=\gamma_i$; the two cases $\gamma_i\le1$ and $\gamma_i>1$ are combined into the single factor $\delta^{-[\gamma_i-1]^+}$.
--
--   Differences from the source:
--   - generalization: the bounds are stated for W = V_i(Ŝ_il) → any real W with δ^(l−1) ≤ W ≤ δ^l; reason: V_i(Ŝ_il) lies in this window by the definition of Ŝ_il; the statement specializes to the page
--   - encoding: δ^l, δ^(l−1) for l ∈ Z and the factors δ^(2γ̄+1), δ^(γ̄+1), δ^(−[a]^+) → zpow for the integer powers, Real.rpow for the real exponents, [a]^+ as max a 0; reason: Lean convention; same values
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 53, between (35) and (36)

import Mathlib

namespace NestedLogitAssort.DeltaGrid

/-- **Bounds on `V_i(Ŝ_{il})^{γ_i − 1}` and `V_i(Ŝ_{il})^{γ_i}` from the window of level `l`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, proof of Theorem 12 (Appendix A.6), p. 53 (unnumbered, between (35) and (36)):
from `δ^{l−1} ≤ V_i(Ŝ_{il}) ≤ δ^l`,
`V_i(Ŝ_{il})^{γ_i−1} ≥ (δ^l)^{γ_i−1} δ^{−[γ_i−1]^+}` and `V_i(Ŝ_{il})^{γ_i} ≤ (δ^l)^{γ_i}`,
where `[a]^+ = max{a, 0}`.

Stated for every real `W` in the window `[δ^{l−1}, δ^l]`; the page applies it to
`W = V_i(Ŝ_{il})`.

**Formalization Note.** `δ ^ l` and `δ ^ (l - 1)` are integer powers (`zpow`); all other powers
are real powers (`Real.rpow`). `W ≥ δ^{l−1} > 0`, so no power of `0` occurs. -/
theorem approx_weight_bounds (δ : ℝ) (hδ : 1 < δ) (γ : ℝ) (hγ : 0 ≤ γ) (l : ℤ) (W : ℝ)
    (hW1 : δ ^ (l - 1) ≤ W) (hW2 : W ≤ δ ^ l) :
    (δ ^ l) ^ (γ - 1) * δ ^ (-(max (γ - 1) 0)) ≤ W ^ (γ - 1) ∧
      W ^ γ ≤ (δ ^ l) ^ γ := by sorry

end NestedLogitAssort.DeltaGrid
