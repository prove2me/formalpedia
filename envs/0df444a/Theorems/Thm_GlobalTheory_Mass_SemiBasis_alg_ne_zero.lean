-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SemiBasis_alg_ne_zero
-- name    : GlobalTheory.Mass.SemiBasis.alg_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:10.579864+00:00
-- url     : https://prove2.me/theorems/b2728acb-086b-40a5-aaea-9a00a75fdf5f
-- title:
--   Semi Basis: alg ne zero
-- statement:
--   The Semi Basis construction uses the alg ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLocDIffSpan.lean#L56-L58

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

theorem GlobalTheory.Mass.SemiBasis.alg_ne_zero {d : ℕ} (hd : 2 ≤ d) {s : 𝓞 K}
    (hs : s ∈ primeTo (d : 𝓞 K)) : algebraMap (𝓞 K) K s ≠ 0 := by sorry
