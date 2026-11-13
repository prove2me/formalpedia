-- Prove2me | Theorems.Thm_HararySachs_Hyper_newtonTr_charpolyRev
-- name    : HararySachs.Hyper.newtonTr_charpolyRev
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T04:34:00.609439+00:00
-- url     : https://prove2.me/theorems/f1d3c303-e588-4f6d-8063-5b98994a1617
-- title:
--   Newton traces of a reversed characteristic polynomial
-- statement:
--   Let $M$ be an $n\times n$ complex matrix and let $\tau_e$ be the Newton traces of $\det(I - \zeta M)$, defined by
--   $$\log\det(I-\zeta M) = -\sum_{e\ge 1}\frac{\tau_e}{e}\,\zeta^e.$$
--   Then $\tau_e = \operatorname{tr}(M^e)$ for every $e \ge 1$.
--
--   This is $\log\det = \operatorname{tr}\log$ written coefficientwise. Over $\mathbb{C}$, $\det(I - \zeta M) = \prod_j (1 - \lambda_j\zeta)$ over the eigenvalues $\lambda_j$, so $\tau_e = \sum_j \lambda_j^e = \operatorname{tr}(M^e)$.
--
--   **Formalization Note** $\det(I - \zeta M)$ is `Matrix.charpolyRev M`, and the Newton traces are `newtonTr`.
-- source:
--   The identity $\log\det = \operatorname{tr}\log$; mission strategy comments 8357894d-0c47-45af-94e5-d71263b245a7 and 5f345eb5-bd58-46fc-8bd2-52a8bf0241e1.

import Mathlib
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

/-- `log det(I - ζ M) = tr log(I - ζ M)`: the Newton traces of `det(1 - X M)` are `tr(M^e)`. -/
theorem newtonTr_charpolyRev {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (e : ℕ) (he : 1 ≤ e) :
    newtonTr M.charpolyRev e = (M ^ e).trace := by
  sorry

end HararySachs.Hyper
