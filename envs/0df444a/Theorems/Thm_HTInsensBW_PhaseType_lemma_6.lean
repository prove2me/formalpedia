-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_lemma_6
-- name    : HTInsensBW.PhaseType.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:42.287975+00:00
-- url     : https://prove2.me/theorems/e2623ecd-613a-40fb-99c5-aef5aaebd43e
-- title:
--   Lemma 6, p. 27 — ½M_r(−S_r^T) + ½(−S_r)M_r − η_r M_r is positive semidefinite for some η_r > 0
-- statement:
--   Let every route $r$ have a law $(\pi_r,S_r)\in\mathcal D$, a weight $\kappa_r>0$ and a base arrival rate $\lambda^{(0)}_r>0$, and let $M_r$ be the block (67) of the constructed inner product. Then for every route $r$ there is a constant $\eta_r>0$ such that the matrix
--   $$\tfrac12M_r(-S_r^T)+\tfrac12(-S_r)M_r-\eta_rM_r$$
--   is positive semidefinite.
--
--   In words, $-S_r^T$ is uniformly "positive" for the inner product $M_r$; this is the source of the constant $\eta_{\min}$ in property (P2') and in the drift bounds.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 27, Lemma 6

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

/-- **Lemma 6, p. 27.** (Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 27, Lemma 6.)
For each route `r` there is `η_r > 0` such that
`½ M_r (-S_rᵀ) + ½ (-S_r) M_r - η_r M_r` is positive semidefinite.

**Formalization Note** Hypotheses `κ_r > 0`, `λ^(0)_r > 0` (standing). -/
theorem lemma_6 {L R : ℕ} (N : BWNetwork L R)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r) :
    ∀ r, ∃ η : ℝ, 0 < η ∧
      ((1 / 2 : ℝ) • (Mr N r * (-subgen (N.D r))ᵀ) + (1 / 2 : ℝ) • ((-subgen (N.D r)) * Mr N r)
        - η • Mr N r).PosSemidef := by sorry

end HTInsensBW.PhaseType
