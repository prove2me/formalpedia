-- Prove2me | Theorems.Thm_HararySachs_Hyper_newtonTr_comp_X_pow
-- name    : HararySachs.Hyper.newtonTr_comp_X_pow
-- status  : Proved
-- author  : @milia
-- created : 2026-11-13T04:34:05.968543+00:00
-- url     : https://prove2.me/theorems/4d5f457d-ce60-446c-b734-72ee3623cd01
-- title:
--   Newton traces under the substitution z = ζ^r
-- statement:
--   Let $R$ be a commutative ring, let $\Phi \in R[z]$ have constant term $1$, and let $r \ge 1$. Then for every $d$,
--   $$\tau_{rd}\bigl(\Phi(\zeta^r)\bigr) = r\,\tau_d(\Phi).$$
--   Over $\mathbb{Q}$ this follows from
--   $$\log\Phi(\zeta^r) = -\sum_d \frac{\tau_d}{d}\,\zeta^{rd} = -\sum_d \frac{r\,\tau_d}{rd}\,\zeta^{rd}.$$
--
--   **Formalization Note** $\Phi(\zeta^r)$ is `Φ.comp (X ^ r)`, and the Newton traces are `newtonTr`.
-- source:
--   Rescaling of the logarithm; mission strategy comments 8357894d-0c47-45af-94e5-d71263b245a7 and 5f345eb5-bd58-46fc-8bd2-52a8bf0241e1.

import Mathlib
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

/-- Substituting `z = ζ^r` multiplies the Newton traces by `r`. -/
theorem newtonTr_comp_X_pow {R : Type*} [CommRing R] (Φ : Polynomial R) (h : Φ.coeff 0 = 1)
    (r : ℕ) (hr : 1 ≤ r) (d : ℕ) :
    newtonTr (Φ.comp (Polynomial.X ^ r)) (r * d) = (r : R) * newtonTr Φ d := by
  sorry

end HararySachs.Hyper
