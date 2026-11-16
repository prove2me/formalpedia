-- Prove2me | Theorems.Thm_GuardedSSSP_Supplement_theorem_F_1
-- name    : GuardedSSSP.Supplement.theorem_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:23:50.811204+00:00
-- url     : https://prove2.me/theorems/7f2aaec2-c15a-42c2-b027-5299e83fb693
-- title:
--   Theorem F.1, p.41 — bottom-up path minima with $O(n+Q+h\log_2(h+1))$ comparisons, $O((n+Q)\alpha(n+Q+2)+h\log_2(h+1))$ work and $O(n)$ space
-- statement:
--   Let $D$ be a rooted tree with $n$ vertices and $h$ leaves. Consider any child-before-parent sequence of operations: $\mathrm{Finish}(v,k)$ supplies the immutable key $k$ of $v$ (each vertex at most once, after all its children), and $\mathrm{Eval}(u)$, on a finished vertex, returns the minimum key from $u$ to its highest finished ancestor, inclusive. If the sequence contains $Q$ evaluations, it can be processed online with
--
--   $$O\big(n+Q+h\log_2(h+1)\big)\ \text{key comparisons},\qquad O\big((n+Q)\,\alpha(n+Q+2)+h\log_2(h+1)\big)\ \text{RAM work},$$
--
--   and $O(n)$ space, where keys may be opaque values accessed only through comparisons and $\alpha$ is an inverse-Ackermann function.
--
--   Precisely: there are an initialization program and a handler program of the base mission's RAM, with no real addition and no real literal, and a constant $C>0$, such that for every tree, every legal sequence and every real keys, every run halts, every Eval run returns the correct minimum, the total number of executed instructions is at most $C((n+Q)\alpha(n+Q+2)+h\log_2(h+1))$, the total number of executed real comparisons is at most $C(n+Q+h\log_2(h+1))$, and at most $Cn$ distinct memory cells are written.
--
--   This structure supplies the residuals $R_e$ of the phase algorithm in any child-before-parent order, which is what Theorem C.1 needs.
--
--   **Formalization Note** Interface: `GuardedSSSP.Supplement.PMOp`, `IsLegalSeq`, `treeInit`, `loadOp`, `handlerStarts`, `evalAnswer`.
--
--   Differences from the source:
--   - reading: any sequence … can be processed (a data structure on the comparison–addition RAM) → an initialization program and a handler program of the base mission's RAM, run online: Init on the tree, then one handler run per operation on the memory left by the previous run; reason: the paper's RAM; each Eval must be answered when issued (Appendix E.1 interleaves evaluations and finishes)
--   - reading: O(·) for comparisons, RAM work and space → one constant C > 0 chosen with the programs, before every tree, sequence and key assignment; reason: the theorem asserts one structure with absolute constants
--   - reading: key comparisons; RAM work; O(n) space → executed rcmp instructions; executed instructions of all runs including Init; distinct memory cells written over all runs; reason: direct counts in the RAM
--   - reading: keys may be opaque held values accessed only through a comparison operation → arbitrary real keys, and neither program contains radd or rzero; reason: without real arithmetic or literals a key can only be copied, loaded, stored and compared, and the instruction set has no casts to the integer bank
--   - reading: O(log)-bit words of the paper's RAM → word bound (n + 2)^c of an n-vertex input, independent of the sequence length; reason: §4.1 ties the word length to the input size; the structure stores O(n) records
--   - encoding: child-before-parent sequence of finishes and Q evaluations → IsLegalSeq: each finish is the first of its vertex and follows finishes of all its children; each eval follows the finish of its vertex; Q = number of evals; reason: the legality conditions of Appendix F
--   - encoding: Eval(u) returns the minimum from u to its highest finished ancestor, inclusive → the minimum (in EReal) of the keys of the finished ancestors of u, inclusive; reason: the finished ancestors of a finished vertex form a contiguous upward segment, so the two sets coincide
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Theorem F.1, p.41 (PDF p.42)

import Mathlib
import Definitions.Def_GuardedSSSP_Machine
import Definitions.Def_Algo2LeanLib_Ackermann
import Definitions.Def_GuardedSSSP_Supplement_RootedTree
import Definitions.Def_GuardedSSSP_Supplement_MachineRuns
import Definitions.Def_GuardedSSSP_Supplement_PathMinimaInterface

namespace GuardedSSSP

namespace Supplement

open GuardedSSSP.Machine

/-- **Theorem F.1** (Bottom-up path minima).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…), Theorem F.1, p.41 (PDF p.42), with the operations defined just
before it.

"On a rooted tree with n vertices and h leaves, any child-before-parent sequence of finishes and Q
evaluations can be processed with O(n + Q + h log₂(h + 1)) key comparisons,
O((n + Q)α(n + Q + 2) + h log₂(h + 1)) RAM work, and O(n) space. Keys may be opaque held values accessed
only through a comparison operation."

There are an initialization program `Init`, a handler program `Hd` of the base comparison–addition RAM,
neither containing a real addition or a real literal, and one constant `C > 0`, such that for every rooted
tree `par` on `n` vertices with root `r` and `h` leaves and every legal sequence `ops` of finishes and `Q`
evaluations with arbitrary real keys, run online (`Init` on the tree, then `Hd` once per operation on the
memory left by the previous run):
1. every run halts, and after each `eval u` run the answer cell holds the minimum key from `u` up to its
   highest finished ancestor;
2. the total number of executed instructions is at most `C((n + Q)α(n + Q + 2) + h log₂(h + 1))`;
3. the total number of executed real comparisons is at most `C(n + Q + h log₂(h + 1))`;
4. the number of distinct memory cells written over all runs is at most `C·n`.

**Formalization Note.**
* Online interface, layouts and legality: `GuardedSSSP.Supplement.PMOp`, `IsLegalSeq`, `treeInit`,
  `loadOp`, `handlerStarts`, `evalAnswer`. Each run uses the word bound `(n + 2)^c` of its program.
* Opaque keys: the programs contain no `radd` and no `rzero`, so a key is only copied, loaded, stored and
  compared; the integer bank sees it only through comparison outcomes.
* Space is counted as the distinct addresses written by the programs over the whole sequence; it may not
  grow with `Q`.
* `α` is `Algo2Lean.Ackermann.alpha`; `log₂` is `Real.logb 2`; `n ≥ 1` holds because `r : Fin n`. -/
theorem theorem_F_1 :
    ∃ (Init Hd : Program) (C : ℝ), 0 < C ∧
      (∀ i ∈ Init.code, Instr.isRealArith i = false) ∧
      (∀ i ∈ Hd.code, Instr.isRealArith i = false) ∧
      ∀ {n : ℕ} (par : Fin n → Fin n) (r : Fin n), IsRootedTree par r →
        ∀ ops : List (PMOp n), IsLegalSeq par r ops →
          Halts Init (wordBound Init n 0) (treeInit par r) ∧
          (∀ σ ∈ handlerStarts Hd (wordBound Hd n 0)
              (finalState Init (wordBound Init n 0) (treeInit par r)) ops,
            Halts Hd (wordBound Hd n 0) σ) ∧
          (∀ (i : ℕ) (u : Fin n) (σ : State), ops[i]? = some (PMOp.eval u) →
            (handlerStarts Hd (wordBound Hd n 0)
              (finalState Init (wordBound Init n 0) (treeInit par r)) ops)[i]? = some σ →
            (((finalState Hd (wordBound Hd n 0) σ).rmem (-2) : ℝ) : EReal) =
              evalAnswer par (ops.take i) u) ∧
          ((haltTime Init (wordBound Init n 0) (treeInit par r) +
              ((handlerStarts Hd (wordBound Hd n 0)
                (finalState Init (wordBound Init n 0) (treeInit par r)) ops).map
                  (haltTime Hd (wordBound Hd n 0))).sum : ℕ) : ℝ) ≤
            C * (((n + ops.countP PMOp.isEval : ℕ) : ℝ) *
                (Algo2Lean.Ackermann.alpha (n + ops.countP PMOp.isEval + 2) : ℝ) +
              (numLeaves par r : ℝ) * Real.logb 2 ((numLeaves par r : ℝ) + 1)) ∧
          ((numCmp Init (wordBound Init n 0) (treeInit par r) +
              ((handlerStarts Hd (wordBound Hd n 0)
                (finalState Init (wordBound Init n 0) (treeInit par r)) ops).map
                  (numCmp Hd (wordBound Hd n 0))).sum : ℕ) : ℝ) ≤
            C * (((n + ops.countP PMOp.isEval : ℕ) : ℝ) +
              (numLeaves par r : ℝ) * Real.logb 2 ((numLeaves par r : ℝ) + 1)) ∧
          ((((handlerStarts Hd (wordBound Hd n 0)
                (finalState Init (wordBound Init n 0) (treeInit par r)) ops).map
                  (writtenInt Hd (wordBound Hd n 0))).foldr (· ∪ ·)
                (writtenInt Init (wordBound Init n 0) (treeInit par r))).card +
            (((handlerStarts Hd (wordBound Hd n 0)
                (finalState Init (wordBound Init n 0) (treeInit par r)) ops).map
                  (writtenReal Hd (wordBound Hd n 0))).foldr (· ∪ ·)
                (writtenReal Init (wordBound Init n 0) (treeInit par r))).card : ℝ) ≤
            C * n := by sorry

end Supplement

end GuardedSSSP
