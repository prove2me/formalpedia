-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisConv_norm_embAll_sq_le
-- name    : GlobalTheory.SW.EisConv.norm_embAll_sq_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:03.868795+00:00
-- url     : https://prove2.me/theorems/689a1676-9605-46fc-99a6-ef90e1ce1140
-- title:
--   Eis Conv: norm emb All sq le
-- statement:
--   The Eis Conv construction uses the norm emb All sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L95-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L95-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem GlobalTheory.SW.EisConv.norm_embAll_sq_le {m : Type} [Fintype m] {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ)
    (w : m → 𝓞 E) : ‖embAll E m w‖ ^ 2 ≤ ∑ τ : Ψ, ∑ j, ‖τ.1 (w j : E)‖ ^ 2 := by sorry
