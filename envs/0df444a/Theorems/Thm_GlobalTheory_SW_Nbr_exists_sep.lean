-- Prove2me | Theorems.Thm_GlobalTheory_SW_Nbr_exists_sep
-- name    : GlobalTheory.SW.Nbr.exists_sep
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:13.011333+00:00
-- url     : https://prove2.me/theorems/0bc2fd7a-5e85-4c48-9588-e30dd2ae5934
-- title:
--   Nbr: exists sep
-- statement:
--   The Nbr construction uses the exists sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L209-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L209-L235

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

theorem GlobalTheory.SW.Nbr.exists_sep {M : ℕ} {Λ : Lt E n} (h : Λ ∈ Vset E n M) (P : Ideal (𝓞 E)) [hP : P.IsMaximal]
    (hP0 : P ≠ ⊥) (f : Λ →ₗ[𝓞 E] 𝓞 E ⧸ P) : ∃ x : Fin n → E, ∀ y : Λ, Int' y x ↔ f y = 0 := by sorry
