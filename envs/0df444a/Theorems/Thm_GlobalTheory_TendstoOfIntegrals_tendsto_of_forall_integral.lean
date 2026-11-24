-- Prove2me | Theorems.Thm_GlobalTheory_TendstoOfIntegrals_tendsto_of_forall_integral
-- name    : GlobalTheory.TendstoOfIntegrals.tendsto_of_forall_integral
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:01:44.460431+00:00
-- url     : https://prove2.me/theorems/0d928c7c-9607-4a11-8ca0-fc43f3091c8e
-- title:
--   Tendsto Of Integrals: tendsto of forall integral
-- statement:
--   The Tendsto Of Integrals construction uses the tendsto of forall integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TendstoOfForallIntegral.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TendstoOfForallIntegral.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TendstoOfForallIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TendstoOfIntegrals
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology

theorem GlobalTheory.TendstoOfIntegrals.tendsto_of_forall_integral {L : Type} [Field L] [NumberField L] {ι : Type} {l : Filter ι}
    (f : ι → FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (b : FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (hf : ∀ (i : ι) (v : HeightOneSpectrum (NumberField.RingOfIntegers L)),
      (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hb : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      (b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hl : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      Tendsto (fun i ↦ (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) →
        a.adicCompletion L) v) l
        (𝓝 ((b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v))) :
    Tendsto f l (𝓝 b) := by sorry
