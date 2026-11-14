-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_elementary_candidate_machine
-- name    : IntegerRootsFN.Main.elementary_candidate_machine
-- status  : Open
-- author  : @fffmath
-- created : 2026-11-13T07:34:10.30329+00:00
-- url     : https://prove2.me/theorems/dae8a1bd-7746-42a8-aea5-d934877f2609
-- title:
--   Pan-free search compilation to a uniform candidate generator
-- statement:
--   Assume the full search guarantee of Proposition A.3: its fixed finite machine outputs the prescribed Graeffe-search candidate list from the dense encoding of the leading truncation, with the stated coverage, cardinality, aggregate size and running-time bounds. Then the search routine can be compiled with leading-coefficient extraction and the three small candidates $-1,0,1$ into a candidate algorithm on the original dense polynomial input.
--
--   Writing $d=\min(n,b)$, the resulting uniform generator contains every integer root, has $O(n)$ candidates and aggregate point size $O(b)$, and runs in
--
--   $$\widetilde O(nb+d^3b^2).$$
--
--   The conclusion concerns unfiltered candidates and may include nonroots and duplicates. All constants and the finite machine precede the varying inputs. The hypothesis and conclusion refer to actual multitape transitions; no Pan approximation result is assumed.
--
--   **Formalization Note.** This is the explicit preprocessing and machine-composition obligation connecting Proposition A.3 to the intermediate candidate specification. The supplied repository proves the corresponding construction and bounds in its Costed model; a proof of this child must also establish the literal machine realization required by this mission.
-- source:
--   https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/WithoutPan.lean#L26-L37 (candidate length), #L61-L91 (generation/filter assembly); https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/WithoutPan/Basic.lean#L92-L140 (leading-part extraction), https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/WithoutPan/Size.lean#L130 (aggregate size), https://github.com/fffmath/IntegerRootFinding/blob/530114e43024123e59ef91398e3cf8cda076556a/IntegerRootFinding/WithoutPan/SearchCost.lean#L165 (candidate cost). Source manuscript Appendix A, Proposition A.3, and proof of Theorem 1.1(a). Finite-machine compilation refinement, explicitly left as a child obligation.

import Definitions.Def_IntegerRootsFN_Main_CandidatePipeline

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem elementary_candidate_machine
    (hsearch : ElementarySearchContract) :
    CandidateAlgorithm (fun n b => (n : ℝ) * b + (min n b : ℕ) ^ 3 * (b : ℝ) ^ 2) := by sorry

end IntegerRootsFN.Main
