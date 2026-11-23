-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_elementary_candidate_runtime
-- name    : IntegerRootsFN.Main.elementary_candidate_runtime
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:34:28.815334+00:00
-- url     : https://prove2.me/theorems/e54434bf-d37d-4994-93cb-f6d546618509
-- title:
--   Finite-machine assembly of the elementary candidate list
-- statement:
--   Assume the elementary-search machine supplied by Proposition A.3, which accepts the already formed dense truncation. There is one fixed deterministic multitape machine that accepts the original dense polynomial word and emits the signed-binary encoding of
--
--   $$C=[-1,0,1]\mathbin{+\!\!+}C',$$
--
--   where $C'$ is the exact deterministic Graeffe-search list. Its actual transition count is uniformly bounded by
--
--   $$\widetilde O\!\left(nb+\min(n,b)^3b^2\right),$$
--
--   with one positive constant and fixed logarithm exponents chosen before every valid input.
--
--   This is the remaining literal compilation obligation: extract the leading $d+1$ coefficients and form the truncated input, invoke the supplied search machine, and concatenate the three signed small candidates. It asserts only execution and output, not the mathematical coverage, cardinality, or point-size properties.
--
--   **Formalization Note.** No correctness oracle or candidate-list advice is supplied. Both the input and output are the mission's actual finite words, and `Runs` requires a halting configuration after a bounded number of concrete transitions.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 13, proof of Theorem 1.1(a), together with the input-formation step on p. 12. See also https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/WithoutPan/Basic.lean#L92-L140 and WithoutPan.lean#L61-L91. The literal finite-machine realization is the compilation refinement explicitly required by the mission.

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem elementary_candidate_runtime
    (hsearch : ElementarySearchContract) :
    ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
      ∀ (n b : ℕ) (f : Polynomial ℤ), Valid f n b →
        Runs M (polynomialWord f n b)
          (integersWord ([-1, 0, 1] ++ searchCandidates f n b))
          (softBound C k l n b
            ((n : ℝ) * b + (min n b : ℕ) ^ 3 * (b : ℝ) ^ 2)) := by sorry
