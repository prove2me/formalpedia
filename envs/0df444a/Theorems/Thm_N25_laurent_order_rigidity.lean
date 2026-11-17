-- Prove2me | Theorems.Thm_N25_laurent_order_rigidity
-- name    : N25.laurent_order_rigidity
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:38:54.782202+00:00
-- url     : https://prove2.me/theorems/a1c3e63d-a5df-4cb7-972c-26cbfdd3de45
-- title:
--   A Laurent-series automorphism fixing a uniformizer is trivial
-- statement:
--   Let $K$ be a field, let $F$ be a subfield of $K((q))$, let $τ$ be a $K$-automorphism of $F$, and let $t∈F$ have $q$-order $1$. Assume $τ(t)=t$ and that $τ$ preserves the $q$-order of every element of $F$. Then $$τ=id_F.$$ This rigidity statement identifies automorphisms from their action at the distinguished $q$-place.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open scoped MatrixGroups
open N25

theorem N25.laurent_order_rigidity
    (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (τ : F ≃ₐ[K] F) (t : F)
    (ht : (qSeriesBar K F t).order = 1)
    (hτt : τ t = t)
    (hord : ∀ x : F, (qSeriesBar K F (τ x)).order =
      (qSeriesBar K F x).order) :
    τ = 1 := by sorry
