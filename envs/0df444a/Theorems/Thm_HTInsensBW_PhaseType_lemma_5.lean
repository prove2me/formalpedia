-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_lemma_5
-- name    : HTInsensBW.PhaseType.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:33.736395+00:00
-- url     : https://prove2.me/theorems/c7174f50-4320-435d-9871-cbe49f6bc04a
-- title:
--   Lemma 5, p. 27 — (1/κ_r)(ρ^(0)_r)^T M_r(−S_r^T) is the all-ones row vector
-- statement:
--   Let every route $r$ have a law $(\pi_r,S_r)\in\mathcal D$, a weight $\kappa_r>0$ and a base arrival rate $\lambda^{(0)}_r>0$, and let $\boldsymbol\rho^{(0)}_r=\lambda^{(0)}_r(-S_r)^{-T}\pi_r^T$ be its phase-load vector and $M_r$ the block (67) of the constructed inner product. Then for every route $r$
--   $$\frac1{\kappa_r}(\boldsymbol\rho^{(0)}_r)^TM_r(-S_r^T)=\mathbf 1^T_{K_r\times1}.$$
--
--   This identity is what makes the projection of $(-S^T)(\boldsymbol\rho^{(0)}-\mathbf n\mathbf x)$ onto $\mathbf b^{(\ell)}$ equal to the unused bandwidth minus the surplus (property (P1')), and it gives the trace computation (86).
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 27, Lemma 5

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **Lemma 5, p. 27.** (Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 27, Lemma 5.)
For each route `r`, `(1/κ_r) (ρ^(0)_r)ᵀ M_r (-S_rᵀ) = 1ᵀ_{K_r×1}`, where `ρ^(0)_r` is the
phase-load vector (62) and the right side is the all-ones row vector.

**Formalization Note** Hypotheses `κ_r > 0`, `λ^(0)_r > 0` (standing, pp. 5, 7). The row vector is
`v ᵥ* A`. -/
theorem lemma_5 {L R : ℕ} (N : BWNetwork L R)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r) :
    ∀ r, (1 / N.κ r) • (phaseLoad (N.D r) (N.lam0 r) ᵥ* (Mr N r * (-subgen (N.D r))ᵀ)) =
      fun _ => (1 : ℝ) := by sorry

end HTInsensBW.PhaseType
