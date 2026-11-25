-- Prove2me | Theorems.Thm_GlobalTheory_SubmoduleCount_card_submodule_and_hom_le
-- name    : GlobalTheory.SubmoduleCount.card_submodule_and_hom_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:15.210822+00:00
-- url     : https://prove2.me/theorems/ac09b2cd-6cb9-417e-8b40-0436063c885b
-- title:
--   Submodule Count: card submodule and hom le
-- statement:
--   The Submodule Count construction uses the card submodule and hom le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardSubmoduleAndHomLe.lean#L85-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardSubmoduleAndHomLe.lean#L85-L100

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.SubmoduleCount
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.SubmoduleCount.card_submodule_and_hom_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (D : Type) [AddCommGroup D] [Module L.O D] [Finite D] (g : ℕ) (x : Fin g → D), Submodule.span L.O (Set.range x) = ⊤ → Nat.card (Submodule L.O D) ≤ Nat.card D ^ g ∧ ∀ (D' : Type) [AddCommGroup D'] [Module L.O D'] [Finite D'], Nat.card (D →ₗ[L.O] D') ≤ Nat.card D' ^ g := by sorry
