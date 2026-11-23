-- Prove2me | Theorems.Thm_GlobalTheory_SW_Nbr_nbOf_spec
-- name    : GlobalTheory.SW.Nbr.nbOf_spec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:12.272842+00:00
-- url     : https://prove2.me/theorems/c70b7ccb-bdf5-4089-9f11-59ae6ee5071c
-- title:
--   Nbr: nb Of spec
-- statement:
--   The Nbr construction uses the nb Of spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L266-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L266-L294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem GlobalTheory.SW.Nbr.nbOf_spec {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ₀ : Lt E n}
    (h : Λ ∈ Vset E n M) (h1 : P • Λ ≤ Λ₀) (h2 : Λ₀ ≤ Λ)
    (h3 : Λ₀.toAddSubgroup.relIndex Λ.toAddSubgroup = q) :
    SD (nbOf P Λ₀) ∧ Λ ⊓ nbOf P Λ₀ = Λ₀ := by sorry
