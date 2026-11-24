-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GermRing_coeff_subst_tyS
-- name    : GlobalTheory.RowLaw.GermRing.coeff_subst_tyS
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:31:29.296043+00:00
-- url     : https://prove2.me/theorems/c78ae2e8-5335-49bf-a031-a3e031816f00
-- title:
--   Germ Ring: coeff subst ty S
-- statement:
--   The Germ Ring construction uses the coeff subst ty S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L54-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGermEqGaugedFormalGroupLawExpIntegral.lean#L54-L87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermEqGaugedFormalGroupLawExpIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.FormalInv MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GermRing
variable {C : Type} [Field C]

theorem GlobalTheory.RowLaw.GermRing.coeff_subst_tyS {τ : Type} {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) {t : MvPowerSeries τ C}
    (ht : constantCoeff t = 0) (μ : τ →₀ ℕ) :
    coeff μ (PowerSeries.subst t (tyS l a)) = ∑ s ∈ Finset.range (μ.degree + 1), a s * coeff μ (t ^ (l ^ s)) := by sorry
