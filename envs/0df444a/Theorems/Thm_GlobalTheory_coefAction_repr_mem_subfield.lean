-- Prove2me | Theorems.Thm_GlobalTheory_coefAction_repr_mem_subfield
-- name    : GlobalTheory.coefAction_repr_mem_subfield
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:05.458545+00:00
-- url     : https://prove2.me/theorems/6a1c2c00-5520-4003-8b03-6737da7dd46a
-- title:
--   Global Theory: coef Action repr mem subfield
-- statement:
--   The Global Theory construction uses the coef Action repr mem subfield property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CoefActionReprMemSubfield.lean#L53-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CoefActionReprMemSubfield.lean#L53-L87

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CoefActionReprMemSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.DIV Formalism.BasicNotions NumberField
open GlobalTheory
open NumberField

theorem GlobalTheory.coefAction_repr_mem_subfield : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (K₀ : Subfield K) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n), (∀ τ x, emb τ x ∈ K₀) → ∀ (g : GL (Fin n) E) i j, (_root_.Formalism.L2.DIV.bVV K lam).repr (_root_.Formalism.L2.DIV.rhoV emb lam g (_root_.Formalism.L2.DIV.bVV K lam j)) i ∈ K₀ ∧ (_root_.Formalism.L2.DIV.bVV K lam).repr (_root_.Formalism.L2.DIV.rhoVr emb lam g (_root_.Formalism.L2.DIV.bVV K lam j)) i ∈ K₀ := by sorry
