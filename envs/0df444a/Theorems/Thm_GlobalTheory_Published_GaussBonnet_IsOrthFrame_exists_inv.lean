-- Prove2me | Theorems.Thm_GlobalTheory_Published_GaussBonnet_IsOrthFrame_exists_inv
-- name    : GlobalTheory.Published.GaussBonnet.IsOrthFrame.exists_inv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:33.057177+00:00
-- url     : https://prove2.me/theorems/8034eab5-a38c-4ebb-878e-9193ed54f501
-- title:
--   Is Orth Frame: exists inv
-- statement:
--   The Is Orth Frame construction uses the exists inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/OfPositiveTrivial.lean#L50-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/OfPositiveTrivial.lean#L50-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStabiliserImageSubgroup
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__OfPositiveTrivial_b4304d4fbed4f169
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions
open scoped Matrix ENNReal
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.GaussBonnet
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.Published.GaussBonnet.IsOrthFrame.exists_inv {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} {P Q : ℕ}
    {B : Matrix (Fin r) (Fin P ⊕ Fin Q) ℂ} (hB : IsOrthFrame τ G B) (hr : P + Q = r) :
    Bᴴ * ((G.map τ).map (starRingEnd ℂ) * B) = Formalism.UG.Jpq P Q ∧
      ∃ C : Matrix (Fin P ⊕ Fin Q) (Fin r) ℂ, C * B = 1 ∧ B * C = 1 := by sorry
