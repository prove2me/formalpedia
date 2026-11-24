-- Prove2me | Theorems.Thm_GlobalTheory_SW_UniSp_local_sp
-- name    : GlobalTheory.SW.UniSp.local_sp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:47.987539+00:00
-- url     : https://prove2.me/theorems/cb0a3d53-6cbd-49a7-a042-45c8fc2f4a9d
-- title:
--   Uni Sp: local sp
-- statement:
--   The Uni Sp construction uses the local sp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L85-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsRationalSymplecticOfUnitaryCmField.lean#L85-L99

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
variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
  {S : Matrix ι K ℂ} {S' : Matrix K ι ℂ}
variable {m o : Type} [Fintype m] [Fintype o] [DecidableEq o]
variable [DecidableEq m]

theorem GlobalTheory.SW.UniSp.local_sp {A B C D : Matrix m m ℂ} (h1 : A * Bᴴ = B * Aᴴ) (h2 : A * Dᴴ = B * Cᴴ + 1)
    (h3 : D * Aᴴ = C * Bᴴ + 1) (h4 : C * Dᴴ = D * Cᴴ) :
    dl B * sw m * (dl A)ᵀ = dl A * (dl B * sw m)ᵀ ∧
    dl A * (sw m * dl D * sw m)ᵀ = dl B * sw m * (sw m * dl C)ᵀ + 1 ∧
    sw m * dl D * sw m * (dl A)ᵀ = sw m * dl C * (dl B * sw m)ᵀ + 1 ∧
    sw m * dl D * sw m * (sw m * dl C)ᵀ = sw m * dl C * (sw m * dl D * sw m)ᵀ := by sorry
