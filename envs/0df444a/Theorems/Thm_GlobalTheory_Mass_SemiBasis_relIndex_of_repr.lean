-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SemiBasis_relIndex_of_repr
-- name    : GlobalTheory.Mass.SemiBasis.relIndex_of_repr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:37.723717+00:00
-- url     : https://prove2.me/theorems/333bbf3f-4126-4a9e-a40a-85012776eb6f
-- title:
--   Semi Basis: rel Index of repr
-- statement:
--   The Semi Basis construction uses the rel Index of repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L175-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L175-L198

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

theorem GlobalTheory.Mass.SemiBasis.relIndex_of_repr {ι : Type} [Fintype ι] (b : Module.Basis ι K V) (L L' : AddSubgroup V)
    (B' : AddSubgroup K) (B : ι → AddSubgroup K)
    (h' : ∀ x, x ∈ L' ↔ ∀ i, b.repr x i ∈ B') (h : ∀ x, x ∈ L ↔ ∀ i, b.repr x i ∈ B i) :
    L.relIndex L' = ∏ i, (B i).relIndex B' := by sorry
