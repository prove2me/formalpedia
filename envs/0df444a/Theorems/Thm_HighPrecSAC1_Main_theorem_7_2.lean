-- Prove2me | Theorems.Thm_HighPrecSAC1_Main_theorem_7_2
-- name    : HighPrecSAC1.Main.theorem_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:29:10.361513+00:00
-- url     : https://prove2.me/theorems/676c7dfc-acc9-4aac-acd9-5cd90d3b9b9e
-- title:
--   Theorem 7.2 — parameter-uniform gap majority
-- statement:
--   For every $B\ge4$ and integers $0\le a<b\le B$, there are polynomial-size Boolean AC circuits for the gap-majority promise: output zero at Hamming weight at most $a$, and one at weight at least $b$. Their depth is
--   $$O\left(1+\frac{\log_2(b/(b-a))}{\log_2\log_2 B}\right).$$
--   One deterministic transducer generates their explicit descriptions from $(1^B,a,b)$ in $O(\log B)$ space. The size, depth and space constants are uniform over all three parameters; there is no constraint inside the gap. This is the parameter-uniform approximate-counting ingredient cited as [CW24, Theorem 14].
--
--   Differences from the source:
--   - encoding: finite circuits, Boolean strings, vectors and entrywise matrix inequalities → Fin-indexed words and gates, real vectors, and the explicit EntryLE matrix relation; reason: these carriers preserve the finite objects and the componentwise order
--   - encoding: polynomial size, L-uniformity and big-O bounds → explicit gate-and-wire size, self-delimiting binary descriptions, one finite transducer with c*(floor(log2(n+1))+1) work cells, and one bound constant before n; reason: the source leaves the equivalent machine and description conventions implicit; fixed source and output overhead changes no asymptotic size class
--   - encoding: gate-count depth and asymptotic circuit bounds → input and constant depth zero, maximum depth over output paths, and asymptotic bounds for n at least 3; reason: the layering uses depth-zero sources; finitely many small input lengths can be absorbed into constants; log log n is positive on the stated bound domain
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Theorem 7.2, printed p. 36 (PDF 37)

import Definitions.Def_HighPrecSAC1_Main_Refinement

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

theorem theorem_7_2 :
    ∃ (C : ∀ B a b : ℕ, BCircuit B 1) (M : TreeEdgeRankPC.Transducer)
    (c d s : ℕ) (D : ℝ), 0 < D ∧
    ∀ B a b, 4 ≤ B → a < b → b ≤ B →
      bSize (C B a b) ≤ c*(B+1)^d ∧
      (bDepth (C B a b) : ℝ) ≤ D*(1 + lg ((b:ℝ)/(b-a)) / lg (lg B)) ∧
      GapMaj a b (C B a b) ∧
      M.ComputesWithin (List.replicate B true ++ [false] ++ codeNat a ++ codeNat b)
        (bDescription (C B a b)) (s*(Nat.log 2 (B+1)+1)) := by sorry

end HighPrecSAC1.Main
