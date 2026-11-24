-- Prove2me | Theorems.Thm_GlobalTheory_SW_ExpSum_add_smul_dir
-- name    : GlobalTheory.SW.ExpSum.add_smul_dir
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:39:30.81667+00:00
-- url     : https://prove2.me/theorems/3b0347fb-1be0-4ee6-a8e7-1784330ce2cb
-- title:
--   Exp Sum: add smul dir
-- statement:
--   The Exp Sum construction uses the add smul dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsHeatThH.lean#L134-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ExpSum
variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open Classical

theorem GlobalTheory.SW.ExpSum.add_smul_dir {m : ℕ} (x : CM Ψ m N) (τ : Ψ) (k : Fin m) (a : Fin N) (s : ℂ) :
    (fun σ => x σ + if σ = τ then Matrix.single k a s else 0 : CM Ψ m N) =
      (HAdd.hAdd (α := CF Ψ m N) (β := CF Ψ m N) x (s • dir Ψ τ k a) : CF Ψ m N) := by sorry
