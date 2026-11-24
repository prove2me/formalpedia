-- Prove2me | Theorems.Thm_GlobalTheory_MulEtaleDvr_isMonHom_mulN
-- name    : GlobalTheory.MulEtaleDvr.isMonHom_mulN
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:41.42677+00:00
-- url     : https://prove2.me/theorems/6c3db743-c4d4-4efb-98e2-429b4a0dc3d6
-- title:
--   Mul Etale Dvr: is Mon Hom mul N
-- statement:
--   The Mul Etale Dvr construction uses the is Mon Hom mul N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsUnitNatCastSections.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsUnitNatCastSections.lean#L21-L25

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

theorem GlobalTheory.MulEtaleDvr.isMonHom_mulN (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom (mulN G n) := by sorry
