-- Prove2me | Theorems.Thm_LineVsPoint_lemma_2_4
-- name    : LineVsPoint.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:05:09.324748+00:00
-- url     : https://prove2.me/theorems/77a9ee1a-7bf0-4cd2-a609-7eebe9e17487
-- title:
--   Lemma 2.4 — a polynomial vanishing on more than $D$ lines is zero
-- statement:
--   **Lemma 2.4.** Let $\mathbb F_q$ be a finite field and $R\in\mathbb F_q[X,Y]$ of total degree at most $D$. If $R(L(t))\equiv 0$ for more than $D$ distinct affine lines $L$ of $\mathbb F_q^2$, then $R=0$.
--
--   Here $L(t)=a_L+tu_L$ is a parameterization of $L$ and $R(L(t))\equiv0$ means that the formal polynomial $R(a_L+tu_L)\in\mathbb F_q[t]$ is zero. This is the extension of the Schwartz–Zippel lemma used in Lemmas 2.5 and 2.7.
--
--   Differences from the source:
--   - encoding: R(L(t)) ≡ 0 in the lines' fixed parameterization → lineRestrict (π.a L) (π.u L) R = 0 for an arbitrary line parameterization π, quantified over all π; reason: the paper's parameterization is arbitrary; formal vanishing on a line does not depend on the parameterization
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 2.4, p.12

import Definitions.Def_LineVsPoint_LineTable
import Definitions.Def_LineVsPoint_lineRestrict

set_option autoImplicit false

universe u

namespace LineVsPoint

/-- **Lemma 2.4.** *Let `R ∈ F_q[X, Y]` have total degree at most `D`. If `R(L(t)) ≡ 0` for more
than `D` distinct affine lines `L`, then `R = 0`.*
Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test*
(manuscript, sha256 328a8943…), Lemma 2.4, p.12.

**Formalization Note.** Lines are lines of `F²` as sets, read in a fixed parameterization `π`
(any one); `R(L(t)) ≡ 0` is the formal identity `R(a_L + t u_L) = 0` in `F[t]`. -/
theorem lemma_2_4 :
    ∀ (F : Type u) [Field F] [Fintype F] (π : LinePar F 2) (R : MvPolynomial (Fin 2) F) (D : ℕ),
      R.totalDegree ≤ D → ∀ U : Finset (Line F 2), D < U.card →
      (∀ L ∈ U, lineRestrict (π.a L) (π.u L) R = 0) → R = 0 := by sorry

end LineVsPoint
