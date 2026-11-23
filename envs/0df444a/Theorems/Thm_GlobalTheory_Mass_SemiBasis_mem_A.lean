-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SemiBasis_mem_A
-- name    : GlobalTheory.Mass.SemiBasis.mem_A
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:12.790799+00:00
-- url     : https://prove2.me/theorems/a449785e-ae8f-436b-a723-7fee0bbd01d3
-- title:
--   Semi Basis: mem A
-- statement:
--   The Semi Basis construction uses the mem A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L51-L54

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

theorem GlobalTheory.Mass.SemiBasis.mem_A {d : ℕ} (hd : 2 ≤ d) (x : K) :
    x ∈ A K hd ↔ ∃ (a s : 𝓞 K) (_ : s ∈ primeTo (d : 𝓞 K)),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ := by sorry
