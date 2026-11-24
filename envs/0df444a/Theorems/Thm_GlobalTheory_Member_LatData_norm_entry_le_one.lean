-- Prove2me | Theorems.Thm_GlobalTheory_Member_LatData_norm_entry_le_one
-- name    : GlobalTheory.Member.LatData.norm_entry_le_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:25:38.588668+00:00
-- url     : https://prove2.me/theorems/12830cce-0c23-49c8-ae1f-aca212508768
-- title:
--   Lat Data: norm entry le one
-- statement:
--   The Lat Data construction uses the norm entry le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDataLattice.lean#L17-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDataLattice.lean#L17-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SingleMemIntVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDataLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix
open GlobalTheory GlobalTheory.Member GlobalTheory.Member.LatData
open GlobalTheory.Up.Definite GlobalTheory.LatFin
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Member.LatData.norm_entry_le_one {Λ : Submodule (𝓞 E) (Fin r → E)} {γ : GL (Fin r) E}
    (hγ : IsUStab (1 : Matrix (Fin r) (Fin r) E) Λ γ) (φ : E →+* ℂ) (a b : Fin r) :
    ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1 := by sorry
