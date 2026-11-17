-- Prove2me | Theorems.Thm_MatMulTimeLP_Supplement_theorem_5_13
-- name    : MatMulTimeLP.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:58:18.485338+00:00
-- url     : https://prove2.me/theorems/134ff038-3fc4-4c5e-9999-9a2eb7fa4010
-- title:
--   Theorem 5.13 — exact labeled row queries with layer-sensitive operation costs
-- statement:
--   There are absolute positive constants $C_{\rm init}$, $C_{\rm qry}$, $C_{\rm val}$ and $C_{\rm lab}$ such that, for every matrix $H\in\mathbb R^{n\times n}$ and every $1\le K\le n$, a persistent exact-real-RAM data structure maintains a vector $x\in\mathbb R^n$ and arbitrary labels $\ell(i)\in\{0,\ldots,K-1\}$ with the following operations:
--
--   1. `Init` sets $x=0$ and every label to $0$ in at most $C_{\rm init}n$ instructions.
--   2. `Query(i)` returns $(Hx)_i$ exactly in at most $C_{\rm qry}(K+|L_{\ge\ell(i)}|)$ instructions.
--   3. `SetValue(i,\xi)` replaces $x_i$ by $\xi$ in at most $C_{\rm val}(K+|L_{>\ell(i)}|)$ instructions.
--   4. `SetLabel(i,c)` replaces $\ell(i)$ by $c$ in at most $C_{\rm lab}(K+|L_{[p,q]}|)$ instructions, where $p=\min\{\ell(i),c\}$ and $q=\max\{\ell(i),c\}$.
--
--   Here every layer set and both endpoints in the fourth bound use the labels before the call. Each operation preserves reachability, the fixed matrix and every state component it is not specified to change, so the clauses hold throughout arbitrary interleavings from initialization. In particular, queries remain exact after any sequence of value and label changes.
--
--   This generic theorem is not specialized to the magnitude labels later used by Algorithm 3.
--
--   **Formalization Note** Coordinates are `Fin n` and new labels are `Fin K`. The matrix is supplied in read-only input memory; this is the paper’s fixed-matrix convention under which initialization costs $O(n)$ rather than the cost of copying $n^2$ entries.
--
--   Differences from the source:
--   - encoding: indices $[n]$ and labels $\{0,\ldots,K-1\}$ → coordinates `Fin n`, new labels `Fin K`, and stored natural labels constrained by `RowValidState`; reason: zero-based finite types express exactly the same index and label sets
--   - encoding: a fixed matrix available to `Init(H,K)` with $O(n)$ initialization and the private cache invariant preserved by every operation → $H$ preloaded in a read-only real-memory prefix, with operation contracts quantified over states reachable from initialization; reason: copying $n^2$ entries would contradict the printed bound, and reachability carries Eq. (12) without exposing the implementation’s private cache layout
--   - encoding: the four big-$O$ operation bounds → positive universal constants chosen before $n,K,H$, the state and call, multiplying the exact pre-call layer counts; reason: explicit quantifier order is the uniform meaning of the source’s asymptotic costs
--   - generalization: for each fixed $H$ there is a data structure → for each $n,K$ one four-program implementation works for every $H$ supplied in input memory; reason: the cache algorithm on pp.33–34 is uniform in the entries of $H$, and specialization gives the source statement
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…), Theorem 5.13, pp.32–34

import Mathlib
import Definitions.Def_MatMulTimeLP_Supplement_LabeledRowQueryStructure

namespace MatMulTimeLP

namespace Supplement

set_option autoImplicit false

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Theorem 5.13, pp.32–34: for every matrix
`H` and `1 ≤ K ≤ n`, a data structure maintains arbitrary `x` and labels in `{0,…,K-1}`;
initialization sets both to zero in `O(n)` work, queries return `(Hx)_i` exactly in
`O(K+|L_{≥ℓ(i)}|)`, value changes cost `O(K+|L_{>ℓ(i)}|)`, and a label change costs
`O(K+|L_[p,q]|)` using the labels before the call and every crossed layer.

**Formalization Note** Coordinates and labels are `Fin n` and `Fin K`; the state stores labels as
naturals and `RowValidState` enforces their range.  `H` is already in the read-only input bank, as
required for the printed `O(n)` initialization.  The four uniform exact-real-RAM programs are
chosen before `H`; every semantic and work clause is required for every valid mutable state, so it
holds throughout arbitrary interleavings. -/
theorem theorem_5_13 :
    ∃ (Cinit Cquery Cvalue Clabel : ℝ),
      0 < Cinit ∧ 0 < Cquery ∧ 0 < Cvalue ∧ 0 < Clabel ∧
      ∀ (n K : ℕ), 1 ≤ K → K ≤ n → ∃ Q : LabeledRowQueryStructure n K,
        ∀ H : Matrix (Fin n) (Fin n) ℝ,
          (∀ ω,
            HaltsFromAt Q.initProgram ω (rowInitState (K := K) H) (Q.initTime H ω) ∧
            Q.Reachable H (Q.initResult H ω) ∧
            RowValidState (K := K) H (Q.initResult H ω) ∧
            rowStateX (n := n) (Q.initResult H ω) = (0 : Fin n → ℝ) ∧
            (∀ i : Fin n, rowStateLabel (n := n) (Q.initResult H ω) i = 0) ∧
            ((Q.initTime H ω + 1 : ℕ) : ℝ) ≤ Cinit * n) ∧
          (∀ (s : State), Q.Reachable H s → ∀ (i : Fin n) (ω : Tape),
            let s' := Q.queryResult s i ω
            HaltsFromAt Q.queryProgram ω (loadRowQuery s i) (Q.queryTime s i ω) ∧
            Q.Reachable H s' ∧ RowValidState (K := K) H s' ∧
            rowStateX (n := n) s' = rowStateX (n := n) s ∧
            (∀ j : Fin n, rowStateLabel (n := n) s' j = rowStateLabel (n := n) s j) ∧
            s'.R (rowOutputAddr n) = H.mulVec (rowStateX (n := n) s) i ∧
            ((Q.queryTime s i ω + 1 : ℕ) : ℝ) ≤
              Cquery * (K + rowLayersGE (n := n) s (rowStateLabel (n := n) s i))) ∧
          (∀ (s : State), Q.Reachable H s →
              ∀ (i : Fin n) (xi : ℝ) (ω : Tape),
            let s' := Q.setValueResult s i xi ω
            HaltsFromAt Q.setValueProgram ω (loadRowSetValue s i xi)
                (Q.setValueTime s i xi ω) ∧
            Q.Reachable H s' ∧ RowValidState (K := K) H s' ∧
            rowStateX (n := n) s' = Function.update (rowStateX (n := n) s) i xi ∧
            (∀ j : Fin n, rowStateLabel (n := n) s' j = rowStateLabel (n := n) s j) ∧
            ((Q.setValueTime s i xi ω + 1 : ℕ) : ℝ) ≤
              Cvalue * (K + rowLayersGT (n := n) s (rowStateLabel (n := n) s i))) ∧
          ∀ (s : State), Q.Reachable H s →
              ∀ (i : Fin n) (c : Fin K) (ω : Tape),
            let a := rowStateLabel (n := n) s i
            let p := min a c
            let q := max a c
            let s' := Q.setLabelResult s i c ω
            HaltsFromAt Q.setLabelProgram ω (loadRowSetLabel s i c)
                (Q.setLabelTime s i c ω) ∧
            Q.Reachable H s' ∧ RowValidState (K := K) H s' ∧
            rowStateX (n := n) s' = rowStateX (n := n) s ∧
            rowStateLabel (n := n) s' =
              Function.update (rowStateLabel (n := n) s) i (c : ℕ) ∧
            ((Q.setLabelTime s i c ω + 1 : ℕ) : ℝ) ≤
              Clabel * (K + rowLayersBetween (n := n) s p q) := by sorry

end Supplement

end MatMulTimeLP
