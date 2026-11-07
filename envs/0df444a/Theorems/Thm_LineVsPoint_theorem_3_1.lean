-- Prove2me | Theorems.Thm_LineVsPoint_theorem_3_1
-- name    : LineVsPoint.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:59.949769+00:00
-- url     : https://prove2.me/theorems/74bea28d-ca2b-41e3-a9a7-d9430cfe030e
-- title:
--   Theorem 3.1 — multiplicative soundness: agreement $c\varepsilon$ above $C(d/q)^{1/3}$
-- statement:
--   **Theorem 3.1.** There are absolute constants $C,c>0$ with the following property. Let $\mathbb F_q$ be a finite field, $m\ge2$ and $d\ge1$, and let $\varepsilon\ge C(d/q)^{1/3}$. Suppose that $f:\mathbb F_q^m\to\mathbb F_q$ and a degree-$d$ line table $\{P_L\}_{L\in\mathcal L_{q,m}}$ satisfy $\mathrm{Acc}(f,\{P_L\})\ge\varepsilon$. Then there is a polynomial $Q\in\mathbb F_q[X_1,\dots,X_m]$ of total degree at most $d$ such that
--
--   $$
--   \mathrm{agr}(f,Q)\ge c\,\varepsilon .
--   $$
--
--   The constants do not depend on $q$, $m$, $d$, $\varepsilon$ or the tables. Applied round by round to modified point tables, this multiplicative bound gives Theorem 1.1.
--
--   Differences from the source:
--   - encoding: a finite field F_q of order q, q an arbitrary prime power → any finite field F : Type u, with q := Fintype.card F; reason: every finite field has prime-power order and every prime power is the order of a finite field; F need not be a prime field
--   - encoding: the lines of F^m_q, each with a parameterization fixed once and for all → Line F m (lines as sets, each counted once) with the parameterization supplied by the line table, the statement quantifying over every parameterization; reason: the paper fixes the parameterization arbitrarily; the uniform distribution over lines is over the sets, as on p.4
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Theorem 3.1, p.14

import Definitions.Def_LineVsPoint_acc
import Definitions.Def_LineVsPoint_agr

set_option autoImplicit false

universe u

namespace LineVsPoint

/-- **Theorem 3.1.** *There are absolute constants `C, c > 0` with the following property. Let
`m ≥ 2` and `d ≥ 1`, and let `ε ≥ C(d/q)^{1/3}`. Suppose that `f : F^m_q → F_q` and a degree-`d`
line table `{P_L}_{L ∈ L_{q,m}}` satisfy `Acc(f, {P_L}) ≥ ε`. Then there is a polynomial
`Q ∈ F_q[X_1, …, X_m]` of total degree at most `d` such that `agr(f, Q) ≥ cε`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Theorem 3.1, p.14.

**Formalization Note.** `C` and `c` are chosen before the field, `m`, `d`, `ε` and the tables. -/
theorem theorem_3_1 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (F : Type u) [Field F] [Fintype F] (m d : ℕ), 2 ≤ m → 1 ≤ d →
      ∀ ε : ℝ, C * ((d : ℝ) / (Fintype.card F : ℝ)) ^ (1 / 3 : ℝ) ≤ ε →
      ∀ (f : (Fin m → F) → F) (P : LineTable F m d), ε ≤ acc f P →
        ∃ Q : MvPolynomial (Fin m) F, Q.totalDegree ≤ d ∧ c * ε ≤ agr f Q := by sorry

end LineVsPoint
