-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_candidate_filtering_machine
-- name    : IntegerRootsFN.Main.candidate_filtering_machine
-- status  : Open
-- author  : @fffmath
-- created : 2026-11-13T07:33:54.071482+00:00
-- url     : https://prove2.me/theorems/01249314-3b08-46e5-8177-d3ef528ef7ff
-- title:
--   Uniform finite-machine exact filtering of short candidate lists
-- statement:
--   Let $F(n,b)\ge nb$ for positive $n,b$. Assume one uniform candidate-generating finite machine whose output contains every integer root, has $O(n)$ entries, and has total evaluation-point size $O(b)$, with actual running time $\widetilde O(F(n,b))$. Assume the exact multipoint-evaluation machine guarantee of Lemma 3.5.
--
--   Then there is one uniform finite multitape machine that outputs exactly the distinct integer roots, in signed binary, with actual running time
--
--   $$\widetilde O(F(n,b)).$$
--
--   The machine and all constants precede every varying polynomial and size parameter. The result applies to any candidate-generating method satisfying the same interface and any dominating scale $F$.
--
--   **Formalization Note.** This child is the reusable machine-composition and exact-filtering obligation. It includes preservation of the original polynomial input, formation of the evaluation input word, exact zero tests, duplicate removal and output writing. The repository proves analogous correctness and costs in its Costed model; this statement additionally requires their realization by the mission's literal finite-machine execution semantics.
-- source:
--   https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/Algorithm/ExactFilter.lean#L110-L132 (exact filtering correctness), #L134-L236 (duplicate-removal and filtering cost); https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/Algorithm/IntegerRoots.lean#L38-L91 (generic stage-cost assembly); source manuscript Lemma 3.5 and final exact-evaluation steps of both clauses of Theorem 1.1. Finite-machine compilation refinement, explicitly left as a child obligation.

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem candidate_filtering_machine
    (F : ℕ → ℕ → ℝ)
    (hscale : ∀ n b : ℕ, 1 ≤ n → 1 ≤ b → (n : ℝ) * b ≤ F n b)
    (heval : MultipointEvaluationContract)
    (hgen : CandidateAlgorithm F) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
        RootRuns A f n b (softBound C k l n b (F n b)) := by sorry

end IntegerRootsFN.Main
