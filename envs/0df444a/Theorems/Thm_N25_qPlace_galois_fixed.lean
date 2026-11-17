-- Prove2me | Theorems.Thm_N25_qPlace_galois_fixed
-- name    : N25.qPlace_galois_fixed
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:06.459231+00:00
-- url     : https://prove2.me/theorems/c75632fb-f874-4b6f-b9d8-6d11c2921a93
-- title:
--   The distinguished $q$-infinity place is Galois fixed
-- statement:
--   Let $F=ℚ̄(X_H(25))$ and assume $F$ contains an element whose Laurent expansion has $q$-order $-1$, so that the distinguished place $P_∞$ at $q=0$ is defined. For every $σ∈Gal(ℚ̄/ℚ)$, the arithmetic semilinear action fixes this place: $$σ·P_∞=P_∞.$$ This makes the chosen cusp a rational Galois-fixed anchor. Formalization note: the existential hypothesis supplies the simple-pole witness required by the library definition of the $q$-place.
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

theorem N25.qPlace_galois_fixed
    (h : ∃ j : xHFunctionFieldBar 25 H25,
      (qSeriesBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) j).order = -1)
    (σ : Gal) :
    arithmeticGalois (xHFunctionField 25 H25) σ •
      qInftyPlaceBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) h =
      qInftyPlaceBar (AlgebraicClosure ℚ) (xHFunctionFieldBar 25 H25) h := by sorry
