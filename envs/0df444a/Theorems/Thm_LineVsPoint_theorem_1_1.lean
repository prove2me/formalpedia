-- Prove2me | Theorems.Thm_LineVsPoint_theorem_1_1
-- name    : LineVsPoint.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:06:17.853096+00:00
-- url     : https://prove2.me/theorems/340953ac-38f4-4bfa-916d-6f904f816ef8
-- title:
--   Theorem 1.1 — acceptance $\varepsilon$ gives agreement $\varepsilon - C(d/q)^{1/3}$
-- statement:
--   **Theorem 1.1.** There is an absolute constant $C>0$ with the following property. Let $\mathbb F_q$ be any finite field, $m\ge 2$ and $d\ge 1$. For every point table $f:\mathbb F_q^m\to\mathbb F_q$ and every degree-$d$ line table $\{P_L\}_{L\in\mathcal L_{q,m}}$ there is a polynomial $Q\in\mathbb F_q[X_1,\dots,X_m]$ of total degree at most $d$ such that
--
--   $$
--   \mathrm{agr}(f,Q):=\Pr_{x\in\mathbb F_q^m}\bigl[Q(x)=f(x)\bigr]\ \ge\ \mathrm{Acc}(f,\{P_L\})-C\Bigl(\frac dq\Bigr)^{1/3}.
--   $$
--
--   Here $\mathrm{Acc}(f,\{P_L\})$ is the probability that a uniformly random incident pair $(x,L)$ satisfies $P_L(x)=f(x)$. The constant $C$ does not depend on $q$, $m$, $d$ or the tables.
--
--   This is the soundness theorem of the line–versus–point low-degree test with the exponent $1/3$, which the paper's Theorem 1.2 shows to be optimal.
--
--   Differences from the source:
--   - encoding: a finite field F_q of order q, q an arbitrary prime power → any finite field F : Type u, with q := Fintype.card F; reason: every finite field has prime-power order and every prime power is the order of a finite field; F need not be a prime field
--   - encoding: the lines of F^m_q, each with a parameterization fixed once and for all → Line F m (lines as sets, each counted once) with the parameterization supplied by the line table, the statement quantifying over every parameterization; reason: the paper fixes the parameterization arbitrarily; the uniform distribution over lines is over the sets, as on p.4
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Theorem 1.1, p.4

import Definitions.Def_LineVsPoint_acc
import Definitions.Def_LineVsPoint_agr

set_option autoImplicit false

universe u

namespace LineVsPoint

/-- **Theorem 1.1.** *There is an absolute constant `C > 0` with the following property. Let
`m ≥ 2` and `d ≥ 1`. For every point table `f : F^m_q → F_q` and degree-`d` line table
`{P_L}_{L ∈ L_{q,m}}`, there is a polynomial `Q ∈ F_q[X_1, …, X_m]` of total degree at most `d`
such that `agr(f, Q) := Pr_{x ∈ F^m_q}[Q(x) = f(x)] ≥ Acc(f, {P_L}) − C(d/q)^{1/3}`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Theorem 1.1, p.4.

**Formalization Note.** `C` is chosen before the field `F` (any finite field, `q = |F|` any
prime power), `m`, `d` and both tables. Lines are sets, each with a parameterization supplied by
the table; `acc` is the uniform incident-pair acceptance probability. Degrees are formal, and the
exponent `1/3` is real. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] (m d : ℕ), 2 ≤ m → 1 ≤ d →
      ∀ (f : (Fin m → F) → F) (P : LineTable F m d),
        ∃ Q : MvPolynomial (Fin m) F, Q.totalDegree ≤ d ∧
          acc f P - C * ((d : ℝ) / (Fintype.card F : ℝ)) ^ (1 / 3 : ℝ) ≤ agr f Q := by sorry

end LineVsPoint
