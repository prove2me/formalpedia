-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_candidate_filtering_composed_run
-- name    : IntegerRootsFN.Main.candidate_filtering_composed_run
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:23:30.34348+00:00
-- url     : https://prove2.me/theorems/efe24240-121e-4683-aa26-9733604c8c47
-- title:
--   Literal candidate/evaluation/filter pipeline with separate stage charges
-- statement:
--   Assume a uniform candidate generator of scale $F$ and the exact multipoint-evaluation contract of Lemma 3.5. There is one finite deterministic multitape machine on the original dense polynomial input which preserves the input, constructs the evaluation record, invokes exact evaluation, tests each resulting integer value for zero, removes duplicate retained candidates, and writes the signed binary output list.
--
--   The machine also exposes the generated candidate list $C$ and uniform natural constants $K_{\rm card},K_{\rm size}$ such that
--
--   $$
--   \forall r\in\mathbb Z,\quad f(r)=0\Longrightarrow r\in C,
--   \qquad |C|\le K_{\rm card}n,
--   \qquad S(C)\le K_{\rm size}b,
--   $$
--
--   where $S(C)=\sum_{c\in C}\lceil\log_2(2+|c|)\rceil$. Its actual transition count is bounded by fixed shifted-logarithmic factors times the unabsorbed stage envelope
--
--   $$
--   F(n,b)+nb+nS(C).
--   $$
--
--   The three terms respectively account for candidate generation, linear input copying and output/list bookkeeping, and exact multipoint evaluation. The output retains exactly those candidates evaluating to zero and removes repetitions. No analytically absorbed $\widetilde O(F)$ comparison or root-output correctness proof is included in this node; those are handled by its parent.
--
--   **Formalization Note.** `Runs` requires actual halting transitions and the exact finite output tape. `List.dedup` supplies the repetition-free filtered list; output order is immaterial. The machine and all constants are chosen uniformly before every valid input.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 11, proof of Theorem 1.1(b), Step 4: exact evaluation of all candidates followed by output of those c with f(c)=0; p. 11 Lemma 3.5 cost O~(nb+nS); generic exact filtering and duplicate removal in https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/Algorithm/ExactFilter.lean#L110-L236 and stage assembly in IntegerRootFinding/Algorithm/IntegerRoots.lean#L38-L91. The literal finite-machine composition is the compilation refinement explicitly left as a mission obligation.

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem candidate_filtering_composed_run
    (F : ℕ → ℕ → ℝ)
    (heval : MultipointEvaluationContract)
    (hgen : CandidateAlgorithm F) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l Kcard Ksize : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
        ∃ cs : List ℤ,
          (∀ r : ℤ, f.IsRoot r → r ∈ cs) ∧
          cs.length ≤ Kcard * n ∧
          pointSize cs ≤ Ksize * b ∧
          Runs A (polynomialWord f n b)
            (integersWord ((cs.filter fun c => f.eval c = 0).dedup))
            (softBound C k l n b
              (F n b + (n : ℝ) * b + n * (pointSize cs : ℝ))) := by sorry
