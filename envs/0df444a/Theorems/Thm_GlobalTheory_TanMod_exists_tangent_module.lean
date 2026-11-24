-- Prove2me | Theorems.Thm_GlobalTheory_TanMod_exists_tangent_module
-- name    : GlobalTheory.TanMod.exists_tangent_module
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:50:07.781237+00:00
-- url     : https://prove2.me/theorems/5a6895df-ca2c-4744-9b7a-674273899c0a
-- title:
--   Tan Mod: exists tangent module
-- statement:
--   The Tan Mod construction uses the exists tangent module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsTangentModuleUniversalGroup.lean#L290-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsTangentModuleUniversalGroup.lean#L290-L303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TanMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem GlobalTheory.TanMod.exists_tangent_module : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module S N) (v : N → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (ρ : 𝓞 E →+* Module.End S N), Function.Injective v ∧ (∀ w, IsTanAt x w ↔ w ∈ Set.range v) ∧ (∀ (n : ℕ) (b : Fin n → N) (a : Fin n → S) w, IsCombAt x (fun i => v (b i)) a w ↔ w = v (∑ i, a i • b i)) ∧ (∀ a m, v (ρ a m) = v m ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (s : S) m, v (s • m) = spMap (epsMul s) ≫ v m := by sorry
