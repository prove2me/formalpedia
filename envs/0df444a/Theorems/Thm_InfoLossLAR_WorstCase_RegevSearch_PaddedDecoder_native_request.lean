-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_PaddedDecoder_native_request
-- name    : InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder.native_request
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:23:27.876441+00:00
-- url     : https://prove2.me/theorems/41529567-480d-48af-b202-cbbf87cdab01
-- title:
--   Uniform quantum evaluation of a polynomial-time encoded request and response
-- statement:
--   Let $T$ be a uniform polynomial-time quantum family. Given polynomial-time classical functions $q$ and $f$, one uniform quantum family accepts a word $w$, runs $T$ on the variable-length request $q(w)$, and returns an encoding with prefix $f(w,o)$ for the measured response $o$. For every pair of events on output words, if a failure on every padded response implies that the response of $T$ is bad, the probability of failure is bounded by the bad-response probability of $T$ on $q(w)$. The construction is independent of both events.
-- source:
--   Auxiliary lemma for the coherent shared-pool Fourier sampler, used to run its BDD family on a framed request at the actual request length. https://prove2.me/theorems/23174e03-6b1d-4113-b6b9-4dab17fa850a

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
open QAlgorithms.Complexity InfoLossLAR.WorstCase OAI.MetricKMedian.Binary.Automatic
open scoped Classical

theorem InfoLossLAR.WorstCase.RegevSearch.PaddedDecoder.native_request (T : MFamily) (hT : IsMQPT T) (q : Str → Str) (hq : Poly q) (f : Str × Str → Str) (hf : Poly f) :
    ∃ C : MFamily, IsMQPT C ∧ ∀ (w : Str) (fail bad : Str → Prop),
      (∀ o tail, fail (f (w,o) ++ tail) → bad o) →
      outputProb C w fail ≤ outputProb T (q w) bad := by sorry
