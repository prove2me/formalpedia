-- Prove2me | Theorems.Thm_GlobalTheory_Member_LatData_exists_data_lattice
-- name    : GlobalTheory.Member.LatData.exists_data_lattice
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:25:39.306336+00:00
-- url     : https://prove2.me/theorems/71bb44bd-f52f-4b4f-8da8-05e45b08fc7a
-- title:
--   Lat Data: exists data lattice
-- statement:
--   The Lat Data construction uses the exists data lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDataLattice.lean#L132-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDataLattice.lean#L132-L209

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
open NumberField
open scoped ComplexConjugate ComplexOrder Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Member.LatData.exists_data_lattice : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ →
    ∃ X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r, X.Λ = Λ := by sorry
