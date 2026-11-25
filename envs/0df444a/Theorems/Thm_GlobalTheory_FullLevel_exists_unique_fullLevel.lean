-- Prove2me | Theorems.Thm_GlobalTheory_FullLevel_exists_unique_fullLevel
-- name    : GlobalTheory.FullLevel.exists_unique_fullLevel
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:22.96197+00:00
-- url     : https://prove2.me/theorems/644993db-4c62-4f23-a2cc-3cb0e9f87c51
-- title:
--   Full Level: exists unique full Level
-- statement:
--   The Full Level construction uses the exists unique full Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniqueFullLevel.lean#L43-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniqueFullLevel.lean#L43-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_WeilIsUniqueOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFullSymplecticLevelStructureUniqueOfLevelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFullSymplecticLevelStructureOfTateIsoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueFullLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.FullLevel.exists_unique_fullLevel {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (β : B →+* k) (hx : x ≫ s = spMap β) (z : kˣ) (hz : IsPrimitiveRoot z l.M')
    (hzA : (z : k) ^ (l.M' / l.A) = β b.ζ) :
    ∃! ev : D.La → (Over.mk x ⟶ o.t.G),
      IsSympLevel D (fun a g => g ≫ o.t.act.act a)
          (fun n g g' c => Out.WeilIs o.t.G o.t.PP.L n g g' (unitOn c)) l.M' z ev ∧
        Induces l (fun a => toUnit _ ≫ o.etaA a) (fun a => toUnit _ ≫ o.eta a) ev := by sorry
