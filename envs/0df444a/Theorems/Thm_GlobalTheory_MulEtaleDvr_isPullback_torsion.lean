-- Prove2me | Theorems.Thm_GlobalTheory_MulEtaleDvr_isPullback_torsion
-- name    : GlobalTheory.MulEtaleDvr.isPullback_torsion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:39.317815+00:00
-- url     : https://prove2.me/theorems/031b7a62-52da-4b20-84cb-3a4498b5e7ff
-- title:
--   Mul Etale Dvr: is Pullback torsion
-- statement:
--   The Mul Etale Dvr construction uses the is Pullback torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsUnitNatCastSections.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsUnitNatCastSections.lean#L32-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsUnitNatCastSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.MulEtaleDvr
variable {S : Scheme.{0}}

theorem GlobalTheory.MulEtaleDvr.isPullback_torsion (G : Over S) [GrpObj G] (n : ℕ) :
    IsPullback (torsion.ι G n).left (torsion G n).hom (mulN G n).left η[G].left := by sorry
