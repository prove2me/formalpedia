-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_elementary_candidate_composed_run
-- name    : IntegerRootsFN.Main.elementary_candidate_composed_run
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:48:31.013141+00:00
-- url     : https://prove2.me/theorems/e4d1e99f-065e-400d-8a7a-d2e1b1922243
-- title:
--   Literal composed run with separate preprocessing and search charges
-- statement:
--   Assume the elementary-search machine of Proposition A.3. There is one literal deterministic multitape machine on the original dense polynomial input which forms the truncation, runs the search, and emits the encoding of the candidate list $[-1,0,1]\mathbin{+\!\!+}C'$. Its actual transition count is bounded by the sum of the two natural stage charges:
--
--   $$
--   \widetilde O(nb)\quad\text{for truncation input formation and output assembly},
--   $$
--   $$
--   \widetilde O(d^3b^2)\quad\text{for the supplied search, with }d=\min(n,b).
--   $$
--
--   The statement deliberately retains these as separate `softBound` terms: the first uses the original parameters $n,b$, while the second uses $d,b$. One common positive constant and common exponents may be chosen uniformly.
--
--   This is solely the concrete machine-construction obligation. The subsequent comparison of the logarithms at $d$ and $n$ is separate.
--
--   **Formalization Note.** `Runs` still requires actual halting transitions and exact output on the finite output tape. No abstract operation is assigned a runtime.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 13, proof of Theorem 1.1(a): run the elementary search on the truncation and form $C=\{0,\pm1\}\cup C'$. Input formation is charged at $O(nb)$ beside the Proposition A.3 search cost $\widetilde O(d^3b^2)$. The literal finite-machine assembly is the compilation refinement explicitly required by the mission.

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem elementary_candidate_composed_run
    (hsearch : ElementarySearchContract) :
    ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
        Runs M (polynomialWord f n b)
          (integersWord ([-1, 0, 1] ++ searchCandidates f n b))
          (softBound C k l n b ((n : ℝ) * b) +
            softBound C k l (min n b) b
              ((min n b : ℕ) ^ 3 * (b : ℝ) ^ 2)) := by sorry
