-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_4_8
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:05:03.408528+00:00
-- url     : https://prove2.me/theorems/d5dad20b-5989-496a-8846-e2563d91d4d3
-- title:
--   Theorem 4.8 — exact certificates on trees, with Corollary 4.10 (monotone separable statistics)
-- statement:
--   Let $G$ be a tree. Consider anchored instances with nonnegative weights, arbitrary $\epsilon\ge0$, arbitrary reports and finite audit intervals; put $q=b+1$ and $\kappa=\min\{b,n-b\}$.
--
--   1. Both endpoints $\ell_I(y),u_I(y)$ and feasible extremal fields attaining them can be computed, or $C_I(y)$ reported empty, with $O(nq(\kappa+1))$ arithmetic operations and $O(nq(\kappa+1))$ space.
--   2. (Corollary 4.10.) Let $F(x)=\sum_{v\in V}f_v(x_v)$ with every $f_v:\mathbb R\to\mathbb R$ nondecreasing and evaluable exactly on an alphabet label in $O(1)$ operations. Both extrema of $F$ over $C_I(y)$ and attaining fields, or infeasibility, can be computed in $O(n(b+1)(\min\{b,n-b\}+1))$ operations and space. No continuity or convexity of the $f_v$ is required.
--
--   Item 2 is the separable clause of the introductory Theorem 1.2.
--
--   **Formalization Note** Item 2 uses one oracle instruction returning $f_v(t)$ at unit cost when $t$ is a label of the full alphabets $A^\pm_v$ (and $0$ otherwise); the program and its constant are fixed before the functions.
--
--   Differences from the source:
--   - encoding: O(·) arithmetic operations (and space) → one fixed program of the unit-cost real RAM and one constant C>0 chosen before every instance, every executed instruction charged, space = distinct cells accessed; reason: the paper's model counts exact arithmetic operations and comparisons; charging all instructions only strengthens the bound
--   - encoding: f_v can be evaluated exactly on an alphabet label in O(1) operations → a unit-cost oracle instruction returning f_v(t) for labels t of the full alphabets A±_v and 0 elsewhere; reason: evaluation on alphabet labels is the only evaluation-cost assumption
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 4.8, printed p.15 (PDF p.17); Corollary 4.10, printed p.16 (PDF p.18); separable clause of Theorem 1.2, printed p.2 (PDF p.4)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_RAM

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 4.8, printed p.15 / PDF p.17, with Corollary 4.10 (printed p.16 / PDF p.18; the
separable clause of introductory Theorem 1.2, printed p.2 / PDF p.4). With `q = b + 1` and
`κ = min{b, n − b}`:
1. one fixed program computes, on every anchored tree instance (nonnegative weights, any
   `ε ≥ 0`, finite audit intervals), both endpoints and two extremal feasible fields, or reports
   `C_I(y)` empty, within `C n q (κ + 1)` operations and `C n q (κ + 1)` cells;
2. one fixed program computes, for every separable `F(x) = ∑_v f_v(x_v)` with every `f_v`
   nondecreasing (no continuity or convexity) and evaluable exactly at alphabet labels in one
   step, both extrema of `F` over `C_I(y)` and attaining fields, or infeasibility, within
   `C n (b + 1)(min{b, n − b} + 1)` operations and cells. Output: `I[0] = 1` iff feasible;
   `R[0] = min F`, `R[1] = max F`, attaining fields at `R[2+v]`, `R[2+n+v]`. -/
theorem theorem_4_8 :
    (∃ (P : Program) (C : ℕ), 0 < C ∧
      ∀ I : Inst, Valid I → Anchored I → I.graph.IsTree →
        ∃ fin, RunsWithin P (fun _ _ => 0) (encInst I).1 (encInst I).2
            (C * I.n * (I.budget + 1) * (min I.budget (I.n - I.budget) + 1))
            (C * I.n * (I.budget + 1) * (min I.budget (I.n - I.budget) + 1)) fin ∧
          CertOutput I fin) ∧
    (∃ (P : Program) (C : ℕ), 0 < C ∧
      ∀ (I : Inst) (f : Fin I.n → ℝ → ℝ), Valid I → Anchored I → I.graph.IsTree →
        (∀ v, Monotone (f v)) →
        ∃ fin, RunsWithin P
            (fun i t => if h : i < I.n then
              (if t ∈ fullUp I ⟨i, h⟩ ∪ fullLow I ⟨i, h⟩ then f ⟨i, h⟩ t else 0) else 0)
            (encInst I).1 (encInst I).2
            (C * I.n * (I.budget + 1) * (min I.budget (I.n - I.budget) + 1))
            (C * I.n * (I.budget + 1) * (min I.budget (I.n - I.budget) + 1)) fin ∧
          (fin.imem 0 = 1 ↔ (CI I).Nonempty) ∧
          ((CI I).Nonempty →
            lowField I.n fin ∈ CI I ∧ upField I.n fin ∈ CI I ∧
            IsLeast ((fun x => ∑ v, f v (x v)) '' CI I) (fin.rmem 0) ∧
            IsGreatest ((fun x => ∑ v, f v (x v)) '' CI I) (fin.rmem 1) ∧
            ∑ v, f v (lowField I.n fin v) = fin.rmem 0 ∧
            ∑ v, f v (upField I.n fin v) = fin.rmem 1)) := by sorry

end MeanCertificates1424.Hardness.Supplement
