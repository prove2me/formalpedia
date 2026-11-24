-- Prove2me | Theorems.Thm_GlobalTheory_ConjugateMembership_mem_iff_conjugate_notMem
-- name    : GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:25:39.830726+00:00
-- url     : https://prove2.me/theorems/b5da41b4-e83d-4a5e-a30e-c1cb8cadccb5
-- title:
--   Conjugate Membership: mem iff conjugate not Mem
-- statement:
--   The Conjugate Membership construction uses the mem iff conjugate not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqIffConjNe.lean#L41-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqIffConjNe.lean#L41-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConjugateMembership
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.ConjugateMembership.mem_iff_conjugate_notMem {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (τ : E →+* ℂ) :
    τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by sorry
