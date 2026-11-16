-- Prove2me | Theorems.Thm_HypercliqueRefutation_FourClique_Supplement_theorem_3_2
-- name    : HypercliqueRefutation.FourClique.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:28:24.219813+00:00
-- url     : https://prove2.me/theorems/ee73641b-f4c5-409d-a806-d4a771b08cee
-- title:
--   Theorem 3.2 — deterministic counting and finding in O(N^3.998)
-- statement:
--   A uniform deterministic algorithm, on every finite $N$-vertex 3-uniform hypergraph, returns the exact number of unordered four-vertex hypercliques and an actual such set if the number is positive. Otherwise it returns a zero count and certifies absence. Its running time is
--
--   $$
--   O\!\left(N^{3998/1000}\right).
--   $$
--
--   The statement uses the published operational count-and-witness problem: input is the dense symmetric Boolean triple indicator with repeated labels zero; output is the exact count, a witness tag and four labels. The program and hidden constants are uniform over sizes and inputs. All $N$, including $N<4$ and sizes that are not powers of two, are covered. There is no fast-multiplication hypothesis. This is a companion theorem with the paper's second exponent; the unchanged mission goal remains the stronger published Theorem 2.8. Lemma 3.1 supports the independent Section 3 proof.
--
--   Differences from the source:
--   - generalization: solve the 3-uniform four-hyperclique problem → return the exact unordered count and one actual four-vertex witness when positive, otherwise certify absence; reason: p.7 states the counting formulation; p.3 supplies logarithmic reporting recovery, absorbed by the strict exponent margin
--   - encoding: deterministic O(N^3.998) time on every finite hypergraph → published operational word-RAM SolvedInTime at the exact rational exponent 3998/1000, with the published dense input and six-cell output; reason: this fixes the machine and output conventions while retaining every size, including zero and sizes that are not powers of two
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026); Theorem 3.2, printed/PDF p.9; algorithm §3.1, pp.8-9; counting formulation p.7.

import Definitions.Def_HypercliqueRefutation_FourClique_CountWitness

set_option autoImplicit false

namespace HypercliqueRefutation.FourClique.Supplement

/-- Chan--Itakura--Ma--Yu, STOC 2027 submission #1431 (October 2026),
    Theorem 3.2, p.9; counting formulation p.7 and reporting convention p.3.
    No power-of-two promise and no multiplication-exponent hypothesis. -/
theorem theorem_3_2 :
    TrulySubcubicAPSP.Problem.SolvedInTime
      HypercliqueRefutation.FourClique.countWitnessProblem (3998 / 1000 : ℚ) := by sorry

end HypercliqueRefutation.FourClique.Supplement
