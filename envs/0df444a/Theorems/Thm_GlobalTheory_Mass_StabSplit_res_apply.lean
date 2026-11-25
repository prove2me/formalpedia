-- Prove2me | Theorems.Thm_GlobalTheory_Mass_StabSplit_res_apply
-- name    : GlobalTheory.Mass.StabSplit.res_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:21.44269+00:00
-- url     : https://prove2.me/theorems/c8179068-a434-5a19-b046-c2c8c76c810c
-- title:
--   Stab Split: res apply
-- statement:
--   The Stab Split construction uses the res apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteUnitaryStabilizerSubspaceProd.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteUnitaryStabilizerSubspaceProd.lean#L71-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteUnitaryStabilizerSubspaceProd
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.StabSplit
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem GlobalTheory.Mass.StabSplit.res_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (g : isom h)
    (hg : g • U = U) (x : U) : (((res h U g hg).1 x : U) : V) = g.1 x := by sorry

attribute [defeq] GlobalTheory.Mass.StabSplit.res_apply
