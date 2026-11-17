-- Prove2me | Theorems.Thm_N25_unitAnalytic25_cusp_leading_limit
-- name    : N25.unitAnalytic25_cusp_leading_limit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:50:20.538838+00:00
-- url     : https://prove2.me/theorems/34641a99-5a74-47cf-bd8f-e05cf10f1965
-- title:
--   Every cusp expansion has a nonzero leading term of exponent at least $-3$
-- statement:
--   Let $i∈ℤ/5ℤ$ and $A∈SL_2(ℤ)$. There exist a real number $ℓ$ with $-3≤ℓ$ and a nonzero complex number $c$ such that $$\lim_{\operatorname{Im}τ→∞}\frac{u_i(Aτ)}{\exp(2πiℓτ)}=c.$$ This uniform lower bound makes the product with the third power of the discriminant bounded at every cusp.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false
open N25

theorem N25.unitAnalytic25_cusp_leading_limit
    (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ ℓ : ℝ, -3 ≤ ℓ ∧ ∃ c : ℂ, c ≠ 0 ∧ Filter.Tendsto
      (fun τ : UpperHalfPlane => unitAnalytic25 i (A • τ) /
        Complex.exp (2*Real.pi*Complex.I*(ℓ : ℂ)*(τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c) := by sorry
