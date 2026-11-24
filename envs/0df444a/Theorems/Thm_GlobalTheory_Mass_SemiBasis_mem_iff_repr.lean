-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SemiBasis_mem_iff_repr
-- name    : GlobalTheory.Mass.SemiBasis.mem_iff_repr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:20:21.135914+00:00
-- url     : https://prove2.me/theorems/b17af04d-c900-4690-9598-ea010cb452e5
-- title:
--   Semi Basis: mem iff repr
-- statement:
--   The Semi Basis construction uses the mem iff repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L161-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L161-L173

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

theorem GlobalTheory.Mass.SemiBasis.mem_iff_repr {d : ℕ} (hd : 2 ≤ d) {ι : Type} (L : Submodule (A K hd) V)
    [Submodule.IsLattice K L] (c : Module.Basis ι (A K hd) L) (x : V) :
    x ∈ L ↔ ∀ i, (c.extendOfIsLattice K).repr x i ∈ A K hd := by sorry
