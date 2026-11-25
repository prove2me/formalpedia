-- Prove2me | Theorems.Thm_GlobalTheory_TanBasisLocal_one_pull
-- name    : GlobalTheory.TanBasisLocal.one_pull
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:31:20.302203+00:00
-- url     : https://prove2.me/theorems/2c1611a9-234f-4a13-9c5c-d10dd155737c
-- title:
--   Tan Basis Local: one pull
-- statement:
--   The Tan Basis Local construction uses the one pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TanBasisLocal.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TanBasisLocal.lean#L45-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsTangentVectorBasisAtPointBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TanBasisLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.TanBasisLocal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem GlobalTheory.TanBasisLocal.one_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    spMap ψ ≫ (1 : Over.mk x ⟶ Xo.univ.t.G).left = (1 : Over.mk (spMap ψ ≫ x) ⟶ Xo.univ.t.G).left := by sorry
