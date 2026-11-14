-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_approximation_candidate_machine
-- name    : IntegerRootsFN.Main.approximation_candidate_machine
-- status  : Open
-- author  : @fffmath
-- created : 2026-11-13T07:34:26.644357+00:00
-- url     : https://prove2.me/theorems/bc03fa83-9f44-46cb-b4ee-a57930add928
-- title:
--   Approximate roots compile to a nearly linear candidate generator
-- statement:
--   Assume the approximation routine of Proposition 3.4, including its literal finite-machine runtime, rational representation-size bound, root coverage and aggregate logarithmic root-size bound. Assume also Lemma 2.2, which transports each integer root of magnitude at least two to a root of the leading truncation within distance two. Then leading-part extraction followed by rational approximation and the seven integer neighbors of each rounded real part yields a uniform candidate generator on the original dense input.
--
--   For every valid degree-$n$ polynomial with coefficient-bit parameter $b$, its list contains every integer root, has $O(n)$ entries and total evaluation-point size $O(b)$, and its actual running time is
--
--   $$\widetilde O(nb).$$
--
--   The constants and one finite multitape machine are uniform. The approximation routine is a hypothesis, so the Pan runtime obligation and its source caveat remain unresolved upstream. The conclusion outputs candidates, without claiming that nonroots have already been removed.
--
--   **Formalization Note.** This is the finite-machine refinement of the repository's candidate-generation theorem. Extraction, parsing, rational rounding, bounded-offset addition and word output must all be implemented and charged; a Costed bound alone does not discharge this child.
-- source:
--   https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/Algorithm/Candidates.lean#L76-L161 (root coverage and count), #L163-L237 (aggregate size), #L409-L465 (cost and candidate-generation theorem), #L468-L476 (candidateGeneration_spec); source manuscript Lemma 2.2 and Proposition 3.4, proof of Theorem 1.1(b). Finite-machine compilation refinement, explicitly left as a child obligation.

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem approximation_candidate_machine
    (happrox : ApproximationRoutineContract)
    (htruncate : TruncationRootContract) :
    CandidateAlgorithm (fun n b => (n : ℝ) * b) := by sorry

end IntegerRootsFN.Main
