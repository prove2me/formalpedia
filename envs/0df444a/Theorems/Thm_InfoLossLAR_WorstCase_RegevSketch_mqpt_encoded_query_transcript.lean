-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_mqpt_encoded_query_transcript
-- name    : InfoLossLAR.WorstCase.RegevSketch.mqpt_encoded_query_transcript
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T15:11:23.126592+00:00
-- url     : https://prove2.me/theorems/1f8e52cf-e894-4f1c-b189-39a31526586c
-- title:
--   Independent measured transcripts for input-dependent nonadaptive quantum queries
-- statement:
--   Fix a uniform multi-output quantum sampler and a native polynomial-time procedure that produces a list of classical queries from the input. A single uniform multi-output circuit family can produce the joint transcript of independent sampler runs on those query strings. The measured register contains a self-delimiting frame with the input and the complete list of designated output words, stored in reverse order and left-padded to the width fixed for that input length. The equation holds for every event of the measured register, with one padding function for all events; its right-hand side sums the independent Born weights over the complete basis outcomes of each run.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, https://homepages.cwi.nl/~rdewolf/qcnotes.pdf, Chapter 2 on uniform quantum circuits, tensor products and measurement. The input-dependent dispatch across circuit descriptions and the framed finite-output representation are specific implementation obligations of the platform circuit model.

import Definitions.Def_InfoLossLAR_LoadedBatchBundle_05
import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
open scoped BigOperators Classical
open QAlgorithms.Complexity InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.RegevSketch

theorem mqpt_encoded_query_transcript
    (G : MFamily) (hG : IsMQPT G) (q : Str → List Str)
    (hq : OAI.MetricKMedian.Binary.Automatic.Poly q) :
    ∃ F : MFamily, IsMQPT F ∧ ∀ w : Str,
      let requests := q w
      let width (i : Fin requests.length) :=
        (requests.get i).length + (G.anc (requests.get i).length + 1)
      ∃ padding : ((i : Fin requests.length) → Bits (width i)) → Str,
        ∀ event : Str → Prop, outputProb F w event =
          ∑ xs : (i : Fin requests.length) → Bits (width i),
            let outs := List.ofFn (fun i => List.ofFn fun j =>
              xs i (G.outW (requests.get i).length j))
            if event (padding xs ++ (encS w ++ encL encS outs).reverse)
            then ∏ i, ‖runLayered (G.circ (requests.get i).length)
              (basisInput (toBits (requests.get i))) (xs i)‖^2 else 0 := by
  sorry

end InfoLossLAR.WorstCase.RegevSketch
