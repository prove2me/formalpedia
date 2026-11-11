-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_theorem_5_2
-- name    : NetUnrelDesign.Main.theorem_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:10:53.344988+00:00
-- url     : https://prove2.me/theorems/00131d11-06b1-4c4d-aa77-b657dc9e6b23
-- title:
--   Theorem 5.2 — ellipsoidal rounding c + JB₂ ⊆ K ⊆ c + Cd²JB₂ from a separation oracle in expected work O(d(S + d²) log(2 + dR/r))
-- statement:
--   There are absolute constants $C,C'>0$ and one program with a separation-oracle instruction such that the following holds. Let $d\ge1$ and let $K\subseteq\mathbb R^d$ be compact and convex, contained in a known Euclidean ball of center $c_0$ and radius $R>0$, and containing some Euclidean ball of radius $r>0$ whose center is not given. Let the separation oracle for $K$ be such that every query costs at most $S$ operations. Given $d$, $c_0$, $R$ and $r$, the program returns, on every halting run, $c$ and a nonsingular matrix $J$ with
--   $$c+JB_2\subseteq K\subseteq c+Cd^2JB_2,\tag{5.12}$$
--   and its expected work is at most $C'd(S+d^2)\log(2+dR/r)$ (5.13). The output always satisfies (5.12); only the number of trials is random.
--
--   Differences from the source:
--
--   - encoding: "there is an algorithm" with an O(·) cost in operations → one Admissible program of the mission's randomized real RAM, fixed with its constant before all inputs; input and output cells as in the statement; expected work = lintegral of total work (∞ on a non-halting run) under the joint law of machine and oracle tapes; reason: the paper's cost model (§1.1) made explicit; O(·) is a constant uniform over inputs
--   - encoding: a separation query for K → a deterministic (tape-independent) oracle that answers 'member' on K and otherwise returns g ≠ 0 with ⟨g, z⟩ ≤ ⟨g, y⟩ for all z ∈ K; every call reports cost ≤ S; reason: a separation oracle is a fixed procedure; the cost bound includes its coordinate transformations
--   - encoding: balls; 'contained in a known ball of radius R' → closed Euclidean balls {‖y − c‖₂ ≤ ρ} with radii R > 0 and r > 0; the outer ball's center c₀ and R, and r, are inputs; reason: a known ball is given by its center and its (positive) radius
--   - encoding: 'the output always satisfies (5.12)' → on every halting run; reason: Las Vegas guarantee
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Theorem 5.2, p. 17 (PDF 18)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Machine
import Definitions.Def_NetUnrelDesign_Main_Interfaces

open scoped BigOperators ENNReal

namespace NetUnrelDesign.Main

/-- **Theorem 5.2 (Ellipsoidal rounding).** There are absolute constants `C, C' > 0` and one program
with a separation-oracle instruction such that, for every dimension `d ≥ 1`, every compact convex
`K ⊆ ℝ^d` contained in a known Euclidean ball `B(c₀, R)` (`R > 0`) and containing some Euclidean ball of radius
`r > 0` (whose center is not given to the program), every deterministic separation oracle for `K`
whose every query costs at most `S` operations: the program, given `d`, `c₀`, `R`, `r`, on every
halting run returns `c` and a nonsingular `J` with `c + JB₂ ⊆ K ⊆ c + Cd²JB₂` (5.12), and its
expected work is at most `C' d(S + d²) log(2 + dR/r)` (5.13). Sun 2026, p. 17 (PDF 18). -/
theorem theorem_5_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ P : Program, Admissible P ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (K : Set (Fin d → ℝ)), IsCompact K → Convex ℝ K →
        ∀ (c0 : Fin d → ℝ) (R r : ℝ), 0 < R → 0 < r → K ⊆ eBall c0 R →
          (∃ c1 : Fin d → ℝ, eBall c1 r ⊆ K) →
          ∀ O : Oracle (sepSpec d), OracleDeterministic (sepSpec d) O → SeparationValid K O →
            ∀ S : ℝ, CostAtMost S O →
              OnEveryHalt P O (initState (sepSpec d) [(d : ℤ)] (vecList c0 ++ [R, r]))
                  (fun s => (outMat s d d).det ≠ 0 ∧
                    ellipsoid (outVec s 0 d) (outMat s d d) 1 ⊆ K ∧
                    K ⊆ ellipsoid (outVec s 0 d) (outMat s d d) (C * (d : ℝ) ^ 2)) ∧
              expectedWork P O (initState (sepSpec d) [(d : ℤ)] (vecList c0 ++ [R, r])) ≤
                ENNReal.ofReal
                  (C' * d * (S + (d : ℝ) ^ 2) * Real.log (2 + d * R / r)) := by sorry

end NetUnrelDesign.Main
