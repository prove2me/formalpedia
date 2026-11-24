-- Prove2me | Theorems.Thm_GlobalTheory_DRFil_indep_of_invariant_isField
-- name    : GlobalTheory.DRFil.indep_of_invariant_isField
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:09.817583+00:00
-- url     : https://prove2.me/theorems/5e82dd6b-9f29-4df3-8425-d6aade8a7117
-- title:
--   DRFil: indep of invariant is Field
-- statement:
--   The DRFil construction uses the indep of invariant is Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndepOfLinearIndependentDdRE.lean#L76-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndepOfLinearIndependentDdRE.lean#L76-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndepOfLinearIndependentDdRE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.DRFil
open GlobalTheory GlobalTheory.DRFil

theorem GlobalTheory.DRFil.indep_of_invariant_isField {G E M ι : Type} [CommRing E] (hE : IsField E) [AddCommGroup M]
    [Module E M] [Fintype ι] (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : ι → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : ι → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0)
    (c : ι → E) (hc : ∑ i, c i • v i = 0) : ∀ i, c i = 0 := by sorry
