-- Prove2me | Theorems.Thm_LineVsPoint_lemma_2_7
-- name    : LineVsPoint.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:08.413813+00:00
-- url     : https://prove2.me/theorems/151ede2f-f9eb-4b37-8dff-450985db65e2
-- title:
--   Lemma 2.7 — lifting from more than $D$ lines through a point
-- statement:
--   **Lemma 2.7** ([HKSS24, Lemma 3.1]). Let $\mathbb F_q$ be a finite field and suppose $B\in\mathbb F_q[X,Y,Z]$ has weighted degree at most $D$ (weights $1,1,d$). Let $b\in\mathbb F_q^2$ and $\alpha\in\mathbb F_q$ satisfy
--
--   $$
--   B(b,\alpha)=0,\qquad B_Z(b,\alpha)\ne0 .
--   $$
--
--   Suppose $\mathcal U$ contains more than $D$ distinct lines through $b$, and each $L\in\mathcal U$ carries a polynomial $P_L$ of degree at most $d$ with $P_L(b)=\alpha$ and $B(L(t),p_L(t))\equiv0$. Then there is a polynomial $Q\in\mathbb F_q[X,Y]$ of total degree at most $d$ such that
--
--   $$
--   B(X,Y,Q(X,Y))\equiv 0\qquad\text{and}\qquad Q|_L=P_L\quad\forall L\in\mathcal U .
--   $$
--
--   Here $p_L$ is $P_L$ in the line's parameterization, and the identities are formal. This is the lifting step that starts the propagation of Lemma 3.5.
--
--   Differences from the source:
--   - encoding: each L ∈ U carries a polynomial P_L of degree ≤ d → a degree-d line table P on F², constrained only on U; reason: every family on U extends to a total table
--   - reading: Q|_L = P_L → the formal identity Q(a_L + t u_L) = p_L(t) in F[t]; reason: §2.1: identities refer to formal polynomials; the proof derives the formal identity (Lemma 2.6 uniqueness); for d < q it coincides with equality of functions on L
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 2.7, p.14

import Definitions.Def_LineVsPoint_LineTable
import Definitions.Def_LineVsPoint_lineRestrict

set_option autoImplicit false

universe u

namespace LineVsPoint

open MvPolynomial in
/-- **Lemma 2.7** (lifting from many lines through a point). *Suppose `B ∈ F_q[X, Y, Z]` has
weighted degree at most `D`. Let `b ∈ F²_q` and `α ∈ F_q` satisfy `B(b, α) = 0`, `B_Z(b, α) ≠ 0`.
Suppose `U` contains more than `D` distinct lines through `b`, and each `L ∈ U` carries a
polynomial `P_L` of degree at most `d` such that `P_L(b) = α`, `B(L(t), p_L(t)) ≡ 0`. Then there is
a polynomial `Q ∈ F_q[X, Y]` of total degree at most `d` such that `B(X, Y, Q(X, Y)) ≡ 0` and
`Q|_L = P_L ∀L ∈ U`.* Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the
Line–versus–Point Test* (manuscript, sha256 328a8943…), Lemma 2.7, p.14.

**Formalization Note.** Weighted degree uses weights `1, 1, d` on `X, Y, Z` (§2.3, p.11).
`P_L(b) = α` is `p_L(t) = α` at the parameter `t` of `b`. `Q|_L = P_L` is the formal identity
`Q(a_L + t u_L) = p_L(t)` in `F[t]`. The polynomials and parameterizations are those of a
degree-`d` line table on `F²`, constrained only on `U`. -/
theorem lemma_2_7 :
    ∀ (F : Type u) [Field F] [Fintype F] (d D : ℕ) (P : LineTable F 2 d)
      (B : MvPolynomial (Fin 3) F) (b : Fin 2 → F) (α : F),
      weightedTotalDegree ![1, 1, d] B ≤ D →
      eval ![b 0, b 1, α] B = 0 → eval ![b 0, b 1, α] (pderiv 2 B) ≠ 0 →
      ∀ U : Finset (Line F 2), D < U.card → (∀ L ∈ U, b ∈ L.carrier) →
      (∀ L ∈ U, (∀ t : F, P.a L + t • P.u L = b → (P.p L).eval t = α) ∧
        graphRestrict (P.a L) (P.u L) (P.p L) B = 0) →
      ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ d ∧ substZ B Q = 0 ∧
        ∀ L ∈ U, lineRestrict (P.a L) (P.u L) Q = P.p L := by sorry

end LineVsPoint
