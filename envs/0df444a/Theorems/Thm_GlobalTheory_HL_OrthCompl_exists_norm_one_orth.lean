-- Prove2me | Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_norm_one_orth
-- name    : GlobalTheory.HL.OrthCompl.exists_norm_one_orth
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:33:06.184304+00:00
-- url     : https://prove2.me/theorems/4aa9835f-d355-4567-810c-b6dd429555e7
-- title:
--   Orth Compl: exists norm one orth
-- statement:
--   The Orth Compl construction uses the exists norm one orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L70-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L70-L92

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
variable {o E : Type*} [CommRing o] [IsLocalRing o] [CommRing E]

theorem GlobalTheory.HL.OrthCompl.exists_norm_one_orth (S : Subring E) (σ : E →+* E) (φ : o →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hσS : ∀ x ∈ S, σ x ∈ S) (hN : ∀ x ∈ S, ∃ c, x * σ x = φ c)
    (hτ : ∃ τ ∈ S, τ + σ τ = 1) (hU : ∀ u : oˣ, ∃ x ∈ S, x * σ x = φ u)
    {y0 y1 y2 c0 c1 c2 : E} (hy0 : y0 ∈ S) (hy1 : y1 ∈ S)
    (hy2 : y2 ∈ S) (hc0 : c0 ∈ S) (hc1 : c1 ∈ S) (hc2 : c2 ∈ S)
    (h : y0 * σ c0 + y1 * σ c1 + y2 * σ c2 = 1) :
    ∃ u0 ∈ S, ∃ u1 ∈ S, ∃ u2 ∈ S, u0 * σ u0 + u1 * σ u1 + u2 * σ u2 = 1 ∧
      u0 * σ y0 + u1 * σ y1 + u2 * σ y2 = 0 := by sorry
