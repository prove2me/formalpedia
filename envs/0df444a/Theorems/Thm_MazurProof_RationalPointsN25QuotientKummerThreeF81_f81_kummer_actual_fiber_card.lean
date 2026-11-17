-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81_kummer_actual_fiber_card
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_actual_fiber_card
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:09.331393+00:00
-- url     : https://prove2.me/theorems/adf39f4f-4014-4bfa-9a53-4f92f9d78d60
-- title:
--   The classifier gives the actual Kummer fiber size
-- statement:
--   Let $e\in\mathbf F_{81}$ be the chosen fifth-cyclotomic element, with canonical denominator $D_e(t)$ and numerator $N_e(t)$. For every $t\in\mathbf F_{81}$, the number of $r\in\mathbf F_{81}$ solving the denominator-cleared Kummer equation equals the executable classifier:
--
--   $$|\{r\in\mathbf F_{81}:r^5D_e(t)+N_e(t)=0\}|=s_{\mathrm{tab}}(t).$$
--
--   This turns the one-variable classifier into an exact count of each Kummer fiber.
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

theorem MazurProof.RationalPointsN25QuotientKummerThreeF81.f81_kummer_actual_fiber_card (t : F81) :
    Nat.card {r : F81 //
      r ^ 5 * canonicalKummerDenominator25Three f81FifthRoot25 t +
        canonicalKummerNumerator25Three f81FifthRoot25 t = 0} =
      f81KummerFiberSize25 t := by sorry
