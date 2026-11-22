-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_uniform_raw_repetitions
-- name    : InfoLossLAR.WorstCase.RegevSearch.uniform_raw_repetitions
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T14:06:32.884798+00:00
-- url     : https://prove2.me/theorems/6e621048-2508-4d8e-b525-8549c3901fc0
-- title:
--   Uniform repeated quantum circuits with classical input preparation and output encoding
-- statement:
--   Fix a uniform polynomial-time family of multi-output quantum circuits. A polynomial-time classical program computes a binary query from the input. A second program produces one slot per desired repetition, and a third encodes a list of measured binary words as a single word.
--
--   There exists one uniform polynomial-time quantum circuit family that realizes these programs and repetitions. On a fixed input, initialize one disjoint copy per slot with the computed query. Write $p(y)$ for the single-copy Born weight of a full computational basis outcome and $u(y)$ for its designated output word. For every event on the final word, its probability equals the sum over all tuples of basis outcomes of their product weights, restricted to tuples for which the encoded list of the $u(y)$, padded on the right with zeros to the output width, belongs to the event. With zero slots the encoder receives the empty list. The number of slots and the length and content of the query may vary among inputs of the same length.
-- source:
--   John Watrous, The Theory of Quantum Information (2018), §2.3.2, p. 105, Eqs. (2.216)–(2.218) and the following product-state observation, https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf#page=48. This supplies the probability identity for disjoint copies. The variable-length scheduling, native polynomial-time programs and exact padded output formulation are the uniform circuit closure obligation for the Prove2Me MFamily model.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open OAI.MetricKMedian.Binary.Automatic
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch

theorem uniform_raw_repetitions (H : MFamily) (hH : IsMQPT H)
    (query slots : Str → Str) (encode : List Str → Str)
    (hq : Poly query) (hs : Poly slots) (he : Poly encode) :
    ∃ G : MFamily, IsMQPT G ∧ ∀ (input q : Str) (copies : ℕ),
      query input = q → (slots input).length = copies → ∀ observe : Str → Prop,
      let raw (y : Bits (q.length + (H.anc q.length + 1))) :=
        List.ofFn (fun j => y (H.outW q.length j))
      let mass (y : Bits (q.length + (H.anc q.length + 1))) :=
        ‖runLayered (H.circ q.length) (basisInput (toBits q)) y‖ ^ 2
      outputProb G input observe =
        ∑ ys : Fin copies → Bits (q.length + (H.anc q.length + 1)),
          (∏ i, mass (ys i)) *
            (let result := encode (List.ofFn (fun i => raw (ys i)))
             if observe (result ++ List.replicate (G.outLen input.length - result.length) false)
             then 1 else 0) := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
