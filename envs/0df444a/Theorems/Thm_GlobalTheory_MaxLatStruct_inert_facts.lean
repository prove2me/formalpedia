-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatStruct_inert_facts
-- name    : GlobalTheory.MaxLatStruct.inert_facts
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:12.981994+00:00
-- url     : https://prove2.me/theorems/4ab52a7a-2b12-48da-9ae8-37e6b7bae939
-- title:
--   Max Lat Struct: inert facts
-- statement:
--   The Max Lat Struct construction uses the inert facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L479-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L479-L509

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct

theorem GlobalTheory.MaxLatStruct.inert_facts {K : Type} [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) {σ : 𝓞 K →+* 𝓞 K}
    (hσ : ∀ r, algebraMap (𝓞 K) K (σ r) = star (algebraMap (𝓞 K) K r)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hin : ∀ r, σ r ∈ P ↔ r ∈ P) :
    (2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2) ∧
      ∀ a b : 𝓞 K, a ∉ P → σ a * b = σ b * a → ∃ w, σ w * w * a + b ∈ P := by sorry
