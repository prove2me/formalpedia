-- Prove2me | Theorems.Thm_LineVsPoint_lemma_2_5
-- name    : LineVsPoint.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:00.696682+00:00
-- url     : https://prove2.me/theorems/bf49a9ab-8d35-41dd-a6bc-7d2a51d69726
-- title:
--   Lemma 2.5 — coprime $U,V$ share at most $uv$ line graphs
-- statement:
--   **Lemma 2.5.** Let $\mathbb F_q$ be a finite field and let $U,V\in\mathbb F_q[X,Y,Z]$ be coprime nonzero polynomials of total degrees $u$ and $v$. Let $\mathcal T$ be a family of affine lines of $\mathbb F_q^2$, each with a univariate polynomial $P_L$ of degree at most $d$, such that
--
--   $$
--   U(L(t),p_L(t))\equiv V(L(t),p_L(t))\equiv 0\qquad\forall L\in\mathcal T.
--   $$
--
--   Then $|\mathcal T|\le uv$.
--
--   Here $p_L\in\mathbb F_q[t]$ is $P_L$ in the line's parameterization and $\equiv0$ is the formal identity in $\mathbb F_q[t]$. In Section 3 the lemma bounds the number of lines deleted in Step 2.
--
--   Differences from the source:
--   - encoding: coprime (only nonzero constants divide both, §2.1) → IsRelPrime U V; reason: IsRelPrime is exactly this notion
--   - encoding: a family T of lines, each with a polynomial P_L of degree ≤ d → a finite set T of lines and a degree-d line table P on F² whose values on T are the P_L; reason: only the lines of T are constrained, and every family on T extends to a total table (e.g. by p_L = 0 elsewhere)
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 2.5, p.13

import Definitions.Def_LineVsPoint_LineTable
import Definitions.Def_LineVsPoint_lineRestrict

set_option autoImplicit false

universe u

namespace LineVsPoint

/-- **Lemma 2.5.** *Let `U, V ∈ F_q[X, Y, Z]` be coprime nonzero polynomials of total degrees `u`
and `v`. Let `T ⊆ L` be a family of affine lines, each with a univariate polynomial `P_L` of
degree at most `d`, such that `U(L(t), p_L(t)) ≡ V(L(t), p_L(t)) ≡ 0 ∀L ∈ T`. Then `|T| ≤ uv`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Lemma 2.5, p.13.

**Formalization Note.** Coprime is `IsRelPrime` (§2.1, p.10). The polynomials `p_L` and the
parameterizations are those of a degree-`d` line table `P` on `F²`; only the lines of `T` are
constrained, so this is the same as giving them on `T` alone. -/
theorem lemma_2_5 :
    ∀ (F : Type u) [Field F] [Fintype F] (d : ℕ) (P : LineTable F 2 d)
      (U V : MvPolynomial (Fin 3) F), U ≠ 0 → V ≠ 0 → IsRelPrime U V →
      ∀ T : Finset (Line F 2),
        (∀ L ∈ T, graphRestrict (P.a L) (P.u L) (P.p L) U = 0 ∧
          graphRestrict (P.a L) (P.u L) (P.p L) V = 0) →
        T.card ≤ U.totalDegree * V.totalDegree := by sorry

end LineVsPoint
