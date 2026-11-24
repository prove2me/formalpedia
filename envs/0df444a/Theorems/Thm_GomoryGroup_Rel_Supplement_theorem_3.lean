-- Prove2me | Theorems.Thm_GomoryGroup_Rel_Supplement_theorem_3
-- name    : GomoryGroup.Rel.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:20:36.384299+00:00
-- url     : https://prove2.me/theorems/777954ec-2da4-41a2-a8fc-92f2f7257293
-- title:
--   THEOREM 3 (corrected: zero-variable bound) — all D values in <7nD steps, one optimal vector in n more steps or all in nD
-- statement:
--   Let $A=(B,N)$ be the integer matrix of the paper, with nonsingular $m\times m$ basis $B$, $n$ nonbasic columns, and all unit columns present in $A$. Let $c=(c_B,c_N)$ be real, suppose the relative costs $c_j^*=c_{N,j}-c_BB^{-1}N_j$ are nonpositive, and put $D=|\det B|$. Suppose the quotient $G=\mathbb Z^m/B\mathbb Z^m$ is supplied as a direct sum of cyclic groups of known orders, with its quotient map $f$ and an enumeration without repetitions. The computation takes the already-known images $f(N_j)$ and relative costs as explicit input arrays; their identifying equalities tie them to the original matrix and costs.
--
--   There are exactly $D$ residue classes in a period. The fixed tabulation procedure returns every optimum value $\varphi(p)$ and a recorded optimal witness for every class, with forward arithmetic count $C$ satisfying
--   $$|G|=D,\qquad C<7nD\ (n>0),\qquad C=0\ (n=0).$$
--   For every integer right-hand side $b$, the returned real value is the greatest objective value of (4), and the returned witness is feasible and optimal. Each recovered vector is a value of the function $y^B$ of (3): it is optimal for (4) and satisfies $\sum_i y_i\le D-1$. From the forward records, one vector $y^B(b)$ is materialized in exactly $n$ additional charged coordinate copies; all $D$ vectors are materialized in exactly $nD$ such copies. Thus every value and both recovery clauses of THEOREM 3 are included.
--
--   This supplies the computational companion to the published periodicity and integer-optimum theorem. It applies to all integer right-hand sides; membership in the reduced basis cone is not required for computing the group problem. No optimal value is defined by a potentially empty real supremum.
--
--   **Formalization Note** Real addition/subtraction/comparison, group addition/subtraction, witness increments and output-coordinate copies are charged individually. Table operations, group-label equality, allocation and loop/index bookkeeping are administrative. The forward procedure has fixed code and no input answer table; all real/group arithmetic in it is traced. Unreachable empty-prefix states replace the faulty finite sentinel. The standard-form representation contains only the quotient data, never an assumption of output correctness. The corrected zero-variable convention keeps the entire source domain. The proof's tie rule (prefer the smaller $T_s$) is not imposed on the algorithm; what the theorem requires of each recovered vector is the property $y^B$ has in (3) and THEOREM 2, optimality with $\sum_i y_i\le D-1$.
--
--   Differences from the source:
--   - correction: The strict forward bound is <7nD without an explicit n=0 convention. → The same strict bound holds for n>0; for n=0 the forward cost is exactly zero.; reason: At n=0 the printed inequality would demand a nonnegative operation count <0. Unit columns force the quotient to be trivial, so no value arithmetic or vector copies are needed; no input is excluded.
--   - correction: The proof allows a finite sentinel M≤min c* at all residues. → The empty-prefix table has value zero at the identity and unreachable cells elsewhere.; reason: With B=(3), N=(1), cB=3, cN=0 and M=-1, residue 2 incorrectly retains -1 instead of -2. The partial optimization problems require unreachable states to be marked until reached.
--   - encoding: Elementary steps are named by example; table lookups are listed separately, and recovery uses proper recording. → A fixed traced algorithm charges real/group arithmetic, witness increments and output-coordinate copies; label equality, table access and loop/index bookkeeping are administrative.; reason: This closes the arithmetic model using precisely specified primitives and fixed code, without an uncharged answer oracle. Standard form, column images and tableau relative costs are supplied input, as in the source.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 262 (PDF 3), THEOREM 3; p. 264 (PDF 5), (8), initialization, recursion tally and recorded backtracking

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting
import Definitions.Def_GomoryGroup_Rel_Supplement_Presentation
import Definitions.Def_GomoryGroup_Rel_Supplement_Tabulation

set_option autoImplicit false

namespace GomoryGroup.Rel.Supplement

/-- THEOREM 3, including all value and recovery bounds. The recovered vectors are
values of y^B: optimal for (4) with Σ y_i ≤ D − 1, the vector used in (3).
At n=0 the impossible literal bound cost < 0 is replaced by cost = 0; no input
case is discarded. -/
theorem theorem_3 {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ)
    (hB : B.det ≠ 0) (hI : HasUnitColumns B N)
    (hopt : ∀ j, reducedCost B N cB cN j ≤ 0)
    (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (P : LatticePresentation B G)
    (images : Fin n → G) (himages : ∀ j, images j = P.quotientMap (fun i => N i j))
    (costs : Fin n → ℝ) (hcosts : costs = reducedCost B N cB cN) :
    let forward := tabulate P.enumeration images costs
    Fintype.card G = detD B ∧
    (if n = 0 then forward.steps = 0 else forward.steps < 7 * n * detD B) ∧
    (∀ p : G, ∃ (z : ℝ) (y : Fin n → ℕ),
      forward.result p = some (z, y) ∧
      ∀ b : Fin m → ℤ, P.quotientMap b = p →
        IsGreatest (groupValues B N cB cN b) z ∧ IsGroupOptimal B N cB cN b y) ∧
    (∀ b : Fin m → ℤ,
      (recoverOne forward.result (P.quotientMap b)).steps = n ∧
      ∃ y : Fin n → ℕ,
        (recoverOne forward.result (P.quotientMap b)).result = some y ∧
        IsGroupOptimal B N cB cN b y ∧ ∑ j, y j ≤ detD B - 1) ∧
    (recoverAll P.enumeration forward.result).steps = n * detD B ∧
    (∀ b : Fin m → ℤ, ∃ y : Fin n → ℕ,
      (recoverAll P.enumeration forward.result).result (P.quotientMap b) = some y ∧
      IsGroupOptimal B N cB cN b y ∧ ∑ j, y j ≤ detD B - 1) := by sorry

end GomoryGroup.Rel.Supplement
