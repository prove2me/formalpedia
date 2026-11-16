-- Prove2me | Theorems.Thm_LineVsPoint_Supplement_theorem_1_2
-- name    : LineVsPoint.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:55:51.383064+00:00
-- url     : https://prove2.me/theorems/4a09cbaf-11ad-4989-93da-dd89eca133ba
-- title:
--   Theorem 1.2 — over $\mathbb F_{s^3}$, tables with acceptance $d/q+(1-d/q)q^{-1/3}+O(q^{-2/3})$ whose global agreement is only $d/q+O(q^{-2/3})$
-- statement:
--   **Theorem 1.2.** There is an absolute constant $C>0$ with the following property. Let $s\ge 3$ be a prime power, let $\mathbb F_q$ be a finite field of order $q=s^3$, and let $m\ge 3$ and $1\le d\le q$ be integers. Then there is a point table $f_d:\mathbb F_q^m\to\mathbb F_q$ such that, for every choice of parameterizations $L(t)=a_L+tu_L$ of the affine lines $L\in\mathcal L_{q,m}$, there is a degree-$d$ line table $\{P^{(d)}_L\}$ (read in those parameterizations) whose acceptance $\varepsilon_{s,d}:=\mathrm{Acc}(f_d,\{P^{(d)}_L\})$ satisfies
--
--   $$
--   \Bigl|\,\varepsilon_{s,d}-\Bigl(\frac dq+\Bigl(1-\frac dq\Bigr)q^{-1/3}\Bigr)\Bigr|\le C\,q^{-2/3},
--   $$
--
--   and such that every polynomial $Q\in\mathbb F_q[X_1,\dots,X_m]$ of total degree at most $d$ satisfies
--
--   $$
--   \mathrm{agr}(f_d,Q)\le \varepsilon_{s,d}-\Bigl(1-\frac dq\Bigr)q^{-1/3}+C\,q^{-2/3}.
--   $$
--
--   Here $\mathrm{Acc}(f,\{P_L\})$ is the probability that a uniformly random incident pair $(x,L)$, $x\in L$, satisfies $P_L(x)=f(x)$, and $\mathrm{agr}(f,Q)$ is the fraction of points $x\in\mathbb F_q^m$ with $Q(x)=f(x)$. The constant $C$ does not depend on $s$, $m$ or $d$.
--
--   This is the lower-bound construction matching Theorem 1.1: acceptance of order $q^{-1/3}$ above $d/q$ is achievable while every degree-$d$ polynomial agrees with the point table on only a $d/q+O(q^{-2/3})$ fraction of points, so the exponent $1/3$ in Theorem 1.1 cannot be improved.
--
--   **Formalization Note** The paper's two $O(q^{-2/3})$ terms are a single constant $C$ quantified before $s$, the field, $m$ and $d$; the acceptance estimate is two-sided. $q$ is the cardinality of the field as a real number and the exponents $-1/3$, $-2/3$ are real. Lines are sets; the line table carries a parameterization, and the statement holds for every parameterization.
--
--   Differences from the source:
--   - encoding: a finite field F_q with q = s^3 → any finite field F : Type u with Fintype.card F = s^3; reason: every such field is F_{s^3} up to isomorphism, and Acc and agr are invariant under field isomorphism
--   - encoding: both O(q^{−2/3}) terms → one absolute constant C > 0 chosen before s, F, m and d, the acceptance bound two-sided (|ε_{s,d} − (d/q + (1 − d/q)q^{−1/3})| ≤ C q^{−2/3}); reason: the standard reading of O(·) in a statement quantified over all s, m, d; the proof is uniform ("uniformly for 1 ≤ d ≤ q", the m > 3 extension costs O(q^{−3}))
--   - encoding: an explicit point table and line table → existence of f_d, and for every line parameterization existence of a line table read in it; reason: "explicit" is not a formal predicate; the paper fixes the parameterization once and for all arbitrarily, so the claim is for every one of them
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a894302fb7d724562b283313f6340ba05f37d1af069246d088f5ff8a1b7b1), Theorem 1.2, pp.4–5 (proof §5, pp.22–26)

import Definitions.Def_LineVsPoint_acc
import Definitions.Def_LineVsPoint_agr

set_option autoImplicit false

universe u

namespace LineVsPoint.Supplement

/-- **Theorem 1.2.** *For every prime power `s ≥ 3`, let `q = s³`. For all integers `m ≥ 3` and
`1 ≤ d ≤ q`, there is an explicit point table `f_d : F^m_q → F_q` and a degree-`d` line table
`{P^{(d)}_L}` with acceptance
`ε_{s,d} := Acc(f_d, {P^{(d)}_L}) = d/q + (1 − d/q) q^{−1/3} + O(q^{−2/3})`
such that every polynomial `Q ∈ F_q[X_1, …, X_m]` of total degree at most `d` satisfies
`agr(f_d, Q) ≤ ε_{s,d} − (1 − d/q) q^{−1/3} + O(q^{−2/3})`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Theorem 1.2, pp.4–5 (proof §5, pp.22–26).

**Formalization Note.** Both `O(q^{−2/3})` terms are one absolute constant `C`, chosen before
`s`, the field `F` (any finite field of order `s³`), `m` and `d`; the acceptance term is
two-sided. "Explicit" is read as existence. The point table `f_d` is chosen before the line
parameterization, and for every parameterization `par` of the lines (which the paper fixes
"once and for all", arbitrarily) there is a degree-`d` line table read in `par`; both clauses
concern that same pair `(f_d, P)`. `q = Fintype.card F` as a real number, with real exponents
`−1/3` and `−2/3`. Degrees are formal. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℕ, IsPrimePow s → 3 ≤ s →
      ∀ (F : Type u) [Field F] [Fintype F], Fintype.card F = s ^ 3 →
      ∀ m d : ℕ, 3 ≤ m → 1 ≤ d → d ≤ Fintype.card F →
      ∃ fd : (Fin m → F) → F, ∀ par : LinePar F m,
        ∃ P : LineTable F m d, P.toLinePar = par ∧
          |acc fd P - ((d : ℝ) / (Fintype.card F : ℝ) +
              (1 - (d : ℝ) / (Fintype.card F : ℝ)) * (Fintype.card F : ℝ) ^ (-(1 / 3 : ℝ)))|
            ≤ C * (Fintype.card F : ℝ) ^ (-(2 / 3 : ℝ)) ∧
          ∀ Q : MvPolynomial (Fin m) F, Q.totalDegree ≤ d →
            agr fd Q ≤ acc fd P -
              (1 - (d : ℝ) / (Fintype.card F : ℝ)) * (Fintype.card F : ℝ) ^ (-(1 / 3 : ℝ)) +
              C * (Fintype.card F : ℝ) ^ (-(2 / 3 : ℝ)) := by sorry

end LineVsPoint.Supplement
