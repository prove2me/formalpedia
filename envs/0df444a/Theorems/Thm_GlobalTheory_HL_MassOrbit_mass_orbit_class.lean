-- Prove2me | Theorems.Thm_GlobalTheory_HL_MassOrbit_mass_orbit_class
-- name    : GlobalTheory.HL.MassOrbit.mass_orbit_class
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:07:25.520448+00:00
-- url     : https://prove2.me/theorems/a8634cf8-a85f-4724-8c7c-3040ea9b334d
-- title:
--   Mass Orbit: mass orbit class
-- statement:
--   The Mass Orbit construction uses the mass orbit class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MassOrbitClass.lean#L15-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MassOrbitClass.lean#L15-L79

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesStabilizerActsOnTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonStabilizerStabilizersCommensurableVolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMassEqSumFrameClasses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MassOrbit

theorem GlobalTheory.HL.MassOrbit.mass_orbit_class {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (r k : ℕ) (S : Frames L r k) (d₁ : S.Datum) (Λ₁ : Submodule L.O S.V)
    (h₁ : S.IsTerm d₁ Λ₁) (d : S.Datum) :
    (S.mass d fun Λ => S.BBzero d Λ ∧ ∃ s ∈ S.St, S.Fr d Λ = s • S.Fr d₁ Λ₁) =
      ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * S.nT d (S.Fr d₁ Λ₁) fun Λ => S.BBzero d Λ := by sorry
