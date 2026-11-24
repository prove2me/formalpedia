-- Prove2me | Theorems.Thm_GlobalTheory_QSA_FinAdele_traceOpen_finiteAdele
-- name    : GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:03:36.29542+00:00
-- url     : https://prove2.me/theorems/6aeec57e-caa7-4d7d-93f6-41eca03f2fcd
-- title:
--   Fin Adele: trace Open finite Adele
-- statement:
--   The Fin Adele construction uses the trace Open finite Adele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenFiniteAdeleRing.lean#L127-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenFiniteAdeleRing.lean#L127-L249

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenFiniteAdeleRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology RestrictedProduct
noncomputable section
open GlobalTheory GlobalTheory.QSA GlobalTheory.QSA.FinAdele
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)}
variable {F : Type} [Field F] [NumberField F]
open NumberField IsDedekindDomain
open scoped Quaternion Topology RestrictedProduct
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : (i : ι) → Set (R i)}
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.QSA.FinAdele.traceOpen_finiteAdele : ∀ (F : Type) [Field F] [NumberField F] (a b : F), (∀ v : HeightOneSpectrum (𝓞 F), _root_.GlobalTheory.QSA.TraceOpen (v.adicCompletion F) (algebraMap F (v.adicCompletion F) a) (algebraMap F (v.adicCompletion F) b)) → (∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F, ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b], _root_.GlobalTheory.QSA.nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧ u.imK ∈ v.adicCompletionIntegers F) → _root_.GlobalTheory.QSA.TraceOpen (FiniteAdeleRing (𝓞 F) F) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a) (algebraMap F (FiniteAdeleRing (𝓞 F) F) b) := by sorry
