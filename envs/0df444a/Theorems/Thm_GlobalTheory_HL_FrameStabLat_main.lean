-- Prove2me | Theorems.Thm_GlobalTheory_HL_FrameStabLat_main
-- name    : GlobalTheory.HL.FrameStabLat.main
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:06:44.484097+00:00
-- url     : https://prove2.me/theorems/2ae75f75-5dc6-4055-86b2-da460413f2a3
-- title:
--   Frame Stab Lat: main
-- statement:
--   The Frame Stab Lat construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroup.lean#L266-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLatticeStabilizerNormalisingSubgroup.lean#L266-L377

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
import Theorems.Thm_GlobalTheory_FrameBasic_main

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem GlobalTheory.HL.FrameStabLat.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', ∃ Λ : Submodule L.O S.V, IsLat L Λ ∧ S.St ⊓ stabL L Λ = S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ⊓ stabL L (Submodule.span L.O (Set.range fun b => n' (S.f' b))) ∧ S.St ⊓ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) ≤ S.St ⊓ stabL L Λ ∧ ∀ h ∈ S.St ⊓ stabL L Λ, CongId L S.ϖ Λ 1 h → h ∈ MulAction.stabilizer S.GLV (S.frameCls (fun b => n (S.f b)) fun b => n' (S.f' b)) := by sorry
