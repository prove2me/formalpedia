-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81KummerNumerator25_eq
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerNumerator25_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:55.932671+00:00
-- url     : https://prove2.me/theorems/c640771d-2eee-4f0c-a967-4a0f2117db7f
-- title:
--   The executable Kummer numerator has the canonical formula
-- statement:
--   Let $e\in\mathbf F_{81}$ be the chosen fifth-cyclotomic element and let $B(e)=e^3+2e^2+2e+1$. For $t\in\mathbf F_{81}$, let $N_{\mathrm{tab}}(t)$ be the table-computed Kummer numerator and let $N_e(t)=t^2(B(e)+e^2t)$ be the canonical numerator. Then
--
--   $$N_{\mathrm{tab}}(t)=N_e(t).$$
--
--   This identifies the executable numerator with the structural Kummer model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitF81Field
import Definitions.Def_N25_ExplicitKummerThree
import Definitions.Def_N25_ExplicitKummerThreeF81

open MazurProof
open MazurProof.RationalPointsN25QuotientKummerThreeF81
open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientKummerThree
open scoped BigOperators
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

theorem MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerNumerator25_eq (t : F81) :
    f81KummerNumerator25 t =
      canonicalKummerNumerator25Three f81FifthRoot25 t := by sorry
