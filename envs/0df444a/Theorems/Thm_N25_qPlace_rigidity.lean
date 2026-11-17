-- Prove2me | Theorems.Thm_N25_qPlace_rigidity
-- name    : N25.qPlace_rigidity
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:01.167902+00:00
-- url     : https://prove2.me/theorems/6641ea74-7fb8-4baa-bc9b-ae75aced5c5d
-- title:
--   A $q$-place-preserving automorphism fixing a simple pole is trivial
-- statement:
--   Let $K$ be a field, let $F⊆K((q))$ be a subfield containing an element of $q$-order $-1$, and let $P_∞$ be its distinguished $q$-place. Let $τ$ be a $K$-automorphism of $F$, and suppose there is $j∈F$ with $ord_q(j)=-1$, $τ(j)=j$, and $τ·P_∞=P_∞$. Then $$τ=id_F.$$ This rigidity identifies automorphisms from the fixed cusp and the distinguished simple-pole function. Formalization note: the first existential witness is bookkeeping for the definition of $P_∞$.
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

theorem N25.qPlace_rigidity
    (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (h : ∃ j : F, (qSeriesBar K F j).order = -1)
    (τ : F ≃ₐ[K] F) (j : F)
    (hj : (qSeriesBar K F j).order = -1)
    (hτj : τ j = j)
    (hfix : SemilinearAut.ofAlgAut τ • qInftyPlaceBar K F h =
      qInftyPlaceBar K F h) :
    τ = 1 := by sorry
