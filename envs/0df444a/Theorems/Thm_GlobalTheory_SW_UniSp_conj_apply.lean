-- Prove2me | Theorems.Thm_GlobalTheory_SW_UniSp_conj_apply
-- name    : GlobalTheory.SW.UniSp.conj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:48:16.465084+00:00
-- url     : https://prove2.me/theorems/ea81efe9-96af-4dfe-9ae6-08e781427a17
-- title:
--   Uni Sp: conj apply
-- statement:
--   The Uni Sp construction uses the conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L147-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L147-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UniSp
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
variable {Ψ : Finset (E →+* ℂ)} {N : ℕ}

theorem GlobalTheory.SW.UniSp.conj_apply (M : Ψ → Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ) (p q : QI E N) :
    (Sm Ψ N * blockDiagonal M * (Sm Ψ N)ᵀ) p q = ∑ τ : Ψ,
      (fun i => Sm Ψ N p (i, τ)) ᵥ* M τ ⬝ᵥ fun i => Sm Ψ N q (i, τ) := by sorry
