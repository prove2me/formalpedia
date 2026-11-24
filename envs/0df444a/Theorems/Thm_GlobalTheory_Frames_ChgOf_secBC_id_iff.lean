-- Prove2me | Theorems.Thm_GlobalTheory_Frames_ChgOf_secBC_id_iff
-- name    : GlobalTheory.Frames.ChgOf.secBC_id_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:52.198796+00:00
-- url     : https://prove2.me/theorems/00a4b23f-39f1-4d27-8f42-cc3e5bb197b6
-- title:
--   Chg Of: sec BC id iff
-- statement:
--   The Chg Of construction uses the sec BC id iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FrameChangeExistsUniqueOfSamePoint.lean#L48-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FrameChangeExistsUniqueOfSamePoint.lean#L48-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeExistsUniqueOfSamePoint
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
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.ChgOf
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

theorem GlobalTheory.Frames.ChgOf.secBC_id_iff {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s t : LB.Sec (PPx x)) :
    SecBC (RingHom.id S) a x x s t ↔ ∀ i, t.f i = scal x a i * s.f i := by sorry
