-- Prove2me | Theorems.Thm_GlobalTheory_SW_Emb_sub_mem
-- name    : GlobalTheory.SW.Emb.sub_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:41:17.115603+00:00
-- url     : https://prove2.me/theorems/1dc33d48-366e-4706-a7fd-2195fb808788
-- title:
--   Emb: sub mem
-- statement:
--   The Emb construction uses the sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EmbeddingCompatibleWithWeilAndDenominator.lean#L403-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EmbeddingCompatibleWithWeilAndDenominator.lean#L403-L436

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EmbeddingCompatibleWithWeilAndDenominator
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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Emb
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}

theorem GlobalTheory.SW.Emb.sub_mem {h : M2 E (N + 1)} (hh : h ∈ UU E (N + 1))
    (hc : ∀ i, h i (Sum.inl 0) = (Pi.single (Sum.inl 0) 1 : Fin (N + 1) ⊕ Fin (N + 1) → E) i) :
    h (Sum.inr 0) = Pi.single (Sum.inr 0) 1 ∧ h.submatrix (up N) (up N) ∈ UU E N := by sorry
