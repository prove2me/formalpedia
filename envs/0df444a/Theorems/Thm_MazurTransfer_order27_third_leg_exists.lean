-- Prove2me | Theorems.Thm_MazurTransfer_order27_third_leg_exists
-- name    : MazurTransfer.order27_third_leg_exists
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T13:37:57.709263+00:00
-- url     : https://prove2.me/theorems/0a47e602-97b4-434b-935c-f8e638f5687b
-- title:
--   The order-27 trisection produces a third rational hauptmodul leg
-- statement:
--   Let $f,\xi\in\mathbb Q$ satisfy $f\ne0,1$, $f^3-6f^2+3f+1\ne0$, and $T(f,\xi)=0$, where $T$ is the fixed trisection polynomial of the marked $X_1(9)$ family. Then there exists $s_3\in\mathbb Q$ such that $G(a_2(f),s_3)=0$, where $G$ is the Fricke-twisted $X_0(9)$ correspondence and $a_2(f)$ is the second family leg. The construction separately proves its denominator factors are nonzero. The named downstream consumer combines this third leg with the rational-chain exclusion to rule out rational points of exact order 27.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: OrderTwentySevenThirdLeg.lean and the complete stage certificates. Kernel dependencies and resolved source-reference ASTs determine the retained source. Each expensive primitive equality retains its original type and uses the corresponding public certificate. All 1954 literal polynomial data functions have checked equality with their originals.

import Mathlib
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData

theorem MazurTransfer.order27_third_leg_exists (f ξ : ℚ)
    (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0)
    (hT : MazurTorsion.Kubert.trisectionPoly f ξ = 0) :
    ∃ s₃ : ℚ, MazurTorsion.Kubert.orderNineG9F
      (MazurTorsion.Kubert.a2legN f / MazurTorsion.Kubert.a2legD f) s₃ = 0 := by sorry
