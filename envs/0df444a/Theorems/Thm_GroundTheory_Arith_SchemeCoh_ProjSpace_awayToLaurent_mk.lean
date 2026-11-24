-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayToLaurent_mk
-- name    : GroundTheory.Arith.SchemeCoh.ProjSpace.awayToLaurent_mk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:54.365073+00:00
-- url     : https://prove2.me/theorems/436f934c-b331-4cf9-a95f-bc2686195172
-- title:
--   Proj Space: away To Laurent mk
-- statement:
--   The Proj Space construction uses the away To Laurent mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L118-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjLaurent.lean#L118-L131

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjSpace
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry MvPolynomial
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
open GroundTheory.Arith.SchemeCoh.ProjSpace
variable {A : Type u} [CommRing A] {n : ℕ}

theorem GroundTheory.Arith.SchemeCoh.ProjSpace.awayToLaurent_mk {p : ℕ} (i : Fin p → Fin (n + 1)) (a : MvPolynomial (Fin (n + 1)) A) (N : ℕ) :
    awayToLaurent i (Localization.mk a (ProjTwist.fpow (xprod i) N)) =
      toLaurent A n a * AddMonoidAlgebra.single (-(N • mult i)) 1 := by sorry
