-- Prove2me | Theorems.Thm_GlobalTheory_LocalExtField_dorbit
-- name    : GlobalTheory.LocalExtField.dorbit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:20:47.956297+00:00
-- url     : https://prove2.me/theorems/e874afdc-fbdc-4ad5-afc5-31bbf660524a
-- title:
--   Local Ext Field: dorbit
-- statement:
--   The Local Ext Field construction uses the dorbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Dorbit.lean#L9-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Dorbit.lean#L9-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Dorbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.LocalExtField
open Polynomial

theorem GlobalTheory.LocalExtField.dorbit : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (β : Ω), ∃ S : Finset Ω, (∀ x, x ∈ S ↔ ∃ d ∈ Dec (F := E) A, d β = x) ∧ ∃ f : Polynomial Ω, f.Monic ∧ f.natDegree = S.card ∧ (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) ∧ f.eval β = 0 := by sorry
