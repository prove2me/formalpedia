-- Prove2me | Theorems.Thm_GlobalTheory_SW_Nbr_nb_move
-- name    : GlobalTheory.SW.Nbr.nb_move
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:44:08.021838+00:00
-- url     : https://prove2.me/theorems/c26e0e20-f4ff-467d-83ba-52cb0b5ecbea
-- title:
--   Nbr: nb move
-- statement:
--   The Nbr construction uses the nb move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L424-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L424-L451

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

theorem GlobalTheory.SW.Nbr.nb_move {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P)
    {h g : Matrix (Fin n) (Fin n) E} (hh : ∀ x y, herm 1 (h *ᵥ x) (h *ᵥ y) = herm 1 x y)
    (hg : h * g = 1) {Λ Λ₁ Λ' Λ₁' : Lt E n} (h₁ : Λ₁ ∈ Vset E n M) (hm : Moves h Λ Λ₁)
    (hm' : Moves h Λ' Λ₁') (h' : Λ' ∈ Nb M P Λ) : Λ₁' ∈ Nb M P Λ₁ := by sorry
