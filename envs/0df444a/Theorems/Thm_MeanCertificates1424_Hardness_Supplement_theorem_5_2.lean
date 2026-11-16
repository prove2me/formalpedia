-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_5_2
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:06:05.262251+00:00
-- url     : https://prove2.me/theorems/621a1d63-d052-43ce-a639-57d384d542cf
-- title:
--   Theorem 5.2 — exact certification for bounded treewidth
-- statement:
--   Given a nice tree decomposition of width $\omega$ with $O(n)$ join nodes and $O((\omega+1)n)$ other nodes, put $q=b+1$ and $\kappa=\min\{b,n-b\}$. For an anchored instance with arbitrary reports, nonnegative weights and finite audit intervals, the endpoints and extremal fields can be computed with
--   $$O\Big(q^{\omega+1}n(\omega+\kappa+1)^2+(n+|E|)q\log\big((n+|E|)q+1\big)\Big)$$
--   arithmetic operations. In particular, exact certification is fixed-parameter tractable in $b+\omega$.
--
--   **Formalization Note** For any constants bounding the numbers of join and other nodes, one program and one constant work for all instances; the fixed-parameter statement is a bound $f(b+\omega)(n+|E|+1)^c$, with $f$ computable, on the same program. An empty feasible class is reported as such.
--
--   Differences from the source:
--   - encoding: O(·) arithmetic operations (and space) → one fixed program of the unit-cost real RAM and one constant C>0 chosen before every instance, every executed instruction charged, space = distinct cells accessed; reason: the paper's model counts exact arithmetic operations and comparisons; charging all instructions only strengthens the bound
--   - reading: the endpoints and extremal fields can be computed → on every anchored instance the program flags whether C_I(y) is nonempty and, if it is, outputs the endpoints and extremal fields; reason: the theorem does not say what happens on an empty class; the dynamic program detects it (no accepted root state, as in Theorem 4.8), so the stronger reading is taken
--   - reading: fixed-parameter tractable in b + ω → time f(b+ω)·(n+|E|+1)^c with f computable, in the arithmetic model, same program; reason: the paper's running times are arithmetic-operation counts
--   - encoding: O(n) join nodes and O((ω+1)n) other nodes → for all constants C₁, C₂, decompositions with at most C₁n join and C₂(ω+1)n other nodes; reason: constants of the hypothesis are quantified before the program
--   - encoding: no space bound stated → cells bounded by 3 per operation; reason: each instruction accesses at most three cells, so this adds no claim
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 5.2, printed p.17 (PDF p.19)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_RAM

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 5.2, printed p.17 / PDF p.19. For all constants `C₁, C₂` (the `O(n)` join nodes
and `O((ω + 1) n)` other nodes), one fixed program and constant `C`: given a nice tree
decomposition of width `ω` with at most `C₁ n` join and `C₂ (ω + 1) n` other nodes, an anchored
instance with arbitrary reports, nonnegative weights and finite audit intervals, and
`q = b + 1`, `κ = min{b, n − b}`, `X = (n + |E|) q`, it computes the endpoints and extremal
fields, or reports `C_I(y)` empty, within `C (q^{ω+1} n (ω + κ + 1)² + X log(X + 1))`
operations; in particular, within `f(b + ω) (n + |E| + 1)^c` operations for a fixed computable
`f` and fixed `c` (fixed-parameter tractable in `b + ω`). Cell counts are bounded by three per
operation. -/
theorem theorem_5_2 (C₁ C₂ : ℕ) :
    ∃ (P : Program) (C : ℕ), 0 < C ∧
      (∀ (I : Inst) (T : NiceTD I.n) (ω : ℕ), Valid I → Anchored I → IsNiceTD I.graph T ω →
        T.joinCount ≤ C₁ * I.n → T.otherCount ≤ C₂ * (ω + 1) * I.n →
        ∃ fin, RunsWithin P (fun _ _ => 0) ((encInst I).1 ++ encTD T) (encInst I).2
            ⌊(C : ℝ) * (((I.budget + 1 : ℕ) : ℝ) ^ (ω + 1) * I.n *
                ((ω + min I.budget (I.n - I.budget) + 1 : ℕ) : ℝ) ^ 2 +
              ((I.n + numEdges I.graph) * (I.budget + 1) : ℕ) *
                Real.log (((I.n + numEdges I.graph) * (I.budget + 1) : ℕ) + 1))⌋₊
            (3 * ⌊(C : ℝ) * (((I.budget + 1 : ℕ) : ℝ) ^ (ω + 1) * I.n *
                ((ω + min I.budget (I.n - I.budget) + 1 : ℕ) : ℝ) ^ 2 +
              ((I.n + numEdges I.graph) * (I.budget + 1) : ℕ) *
                Real.log (((I.n + numEdges I.graph) * (I.budget + 1) : ℕ) + 1))⌋₊) fin ∧
          CertOutput I fin) ∧
      ∃ (f : ℕ → ℕ) (c : ℕ), Computable f ∧
        ∀ (I : Inst) (T : NiceTD I.n) (ω : ℕ), Valid I → Anchored I → IsNiceTD I.graph T ω →
          T.joinCount ≤ C₁ * I.n → T.otherCount ≤ C₂ * (ω + 1) * I.n →
          ∃ fin, RunsWithin P (fun _ _ => 0) ((encInst I).1 ++ encTD T) (encInst I).2
              (f (I.budget + ω) * (I.n + numEdges I.graph + 1) ^ c)
              (3 * (f (I.budget + ω) * (I.n + numEdges I.graph + 1) ^ c)) fin ∧
            CertOutput I fin := by sorry

end MeanCertificates1424.Hardness.Supplement
