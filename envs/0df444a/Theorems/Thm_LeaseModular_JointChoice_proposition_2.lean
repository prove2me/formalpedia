-- Prove2me | Theorems.Thm_LeaseModular_JointChoice_proposition_2
-- name    : LeaseModular.JointChoice.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:14.729989+00:00
-- url     : https://prove2.me/theorems/401484e0-3b5c-4516-b832-ff49e02302a8
-- title:
--   Proposition 2, p. 16 — for γ < 1 the cost threshold for leasing to beat selling is lower under modularity: C_M < C_I
-- statement:
--   Let $0<\delta_2<\delta_1<1$ be the module durabilities under selling and let $0<\gamma<1$ be the relative return condition of off-lease modules. Then the cost thresholds of p. 36 satisfy
--   $$C_M(\delta_1,\delta_2,\gamma)<C_I(\delta_1,\delta_2,\gamma).$$
--
--   Since leasing beats selling under architecture $j$ exactly below $C_j$ (for $\gamma<1$), modularity makes leasing less attractive: adopting a modular architecture can move a leasing firm to selling, but not the reverse.
--
--   **Formalization Note.** The statement concerns the threshold formulas only, so it takes just the parameter inequalities it needs rather than the full standing assumptions (the cost $c$ does not enter).
-- source:
--   Agrawal, Atasu & Ülkü, Leasing, Modularity, and the Circular Economy, author manuscript (Management Science, doi:10.1287/mnsc.2020.3829), Proposition 2, p. 16 (proof: Appendix p. 36)

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

namespace LeaseModular.JointChoice

/-- Proposition 2, p. 16. For `0 < δ₂ < δ₁ < 1` and `0 < γ < 1`, the cost threshold for leasing
to beat selling is lower under a modular architecture: `C_M(δ₁, δ₂, γ) < C_I(δ₁, δ₂, γ)`. -/
theorem proposition_2 (δ₁ δ₂ γ : ℝ) (h₂ : 0 < δ₂) (h₂₁ : δ₂ < δ₁) (h₁ : δ₁ < 1)
    (hγ₀ : 0 < γ) (hγ : γ < 1) :
    CM δ₁ δ₂ γ < CI δ₁ δ₂ γ := by sorry

end LeaseModular.JointChoice
