-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SemiBasis_mem_locD_one
-- name    : GlobalTheory.Mass.SemiBasis.mem_locD_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:20:02.306809+00:00
-- url     : https://prove2.me/theorems/475aa2f4-d9c5-4b0c-b873-2dfa9748f546
-- title:
--   Semi Basis: mem loc D one
-- statement:
--   The Semi Basis construction uses the mem loc D one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L136-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L136-L150

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

theorem GlobalTheory.Mass.SemiBasis.mem_locD_one {d : ℕ} (hd : 2 ≤ d) (x : K) :
    x ∈ locD (d : 𝓞 K) (1 : Submodule (𝓞 K) K) ↔ x ∈ A K hd := by sorry
