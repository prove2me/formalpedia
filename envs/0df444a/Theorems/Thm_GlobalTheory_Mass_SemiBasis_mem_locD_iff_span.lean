-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SemiBasis_mem_locD_iff_span
-- name    : GlobalTheory.Mass.SemiBasis.mem_locD_iff_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:58.271691+00:00
-- url     : https://prove2.me/theorems/de810c2b-5ece-4175-aa69-60eba63cbc5f
-- title:
--   Semi Basis: mem loc D iff span
-- statement:
--   The Semi Basis construction uses the mem loc D iff span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L106-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L106-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SemiBasis
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.Mass.SemiBasis.mem_locD_iff_span {d : ℕ} (hd : 2 ≤ d) (M : Submodule (𝓞 K) V) (x : V) :
    x ∈ locD (d : 𝓞 K) M ↔ x ∈ Submodule.span (A K hd) (M : Set V) := by sorry
