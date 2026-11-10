-- Prove2me | Theorems.Thm_NetworkSumSecure_Solvability_lemma_A_1
-- name    : NetworkSumSecure.Solvability.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:04:31.420141+00:00
-- url     : https://prove2.me/theorems/907ca72f-5c08-47da-8914-61f9ab27b06d
-- title:
--   Lemma A.1 — affine intersection nonemptiness is independent of the sum
-- statement:
--   Let $F$ be a finite field, $U$ a finite user index set, $z_i\ge0$ key counts, $G$ a family of encoding columns, and $W$ a finite set of observed edges. In the appendix coordinate order, write $M_a=\{mG_W^{(m)}:\sum_i m_i=a\}$ and $V_k=\langle G_W^{(k)}\rangle_{\rm row}$. Let $\lambda$ select the sum of all message coordinates. Suppose $\lambda\notin\langle G_W\rangle$. For every observation $y\in F^W$ and all $a,b\in F$,
--
--   $$M_a\cap(y+V_k)\ne\varnothing\quad\Longleftrightarrow\quad M_b\cap(y+V_k)\ne\varnothing.$$
--
--   No intersection is assumed nonempty; observations outside the encoding image are included. This lemma is the appendix prerequisite for the security equivalence in Theorem 5.
--
--   Differences from the source:
--   - generalization: columns induced by a network scheme in Appendix A → arbitrary encoding columns with the same user-message and key coordinates; reason: the linear-algebra argument (76)–(77) needs only the stated target-column exclusion and specializes to every locally induced matrix
--   - encoding: message rows followed by key rows, with an affine translate y+V_k → an explicit coordinate equivalence and membership v-y in the key-row span; reason: the coordinate permutation and subtraction characterize exactly the same affine intersection
--   - generalization: the global sufficiently-large-field and nonempty-participant conventions → every finite field and arbitrary finite user types, with only W required finite in the ambient column family; reason: the argument (76)–(77) needs no field-size bound or network topology; with no users the target-column exclusion is impossible
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), p. 28 (PDF p. 30); standing context p. 27 (PDF p. 29), proof p. 29 (PDF p. 31), Lemma A.1, equations (73)–(77)

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_algebra

namespace NetworkSumSecure.Solvability

/-- Appendix A, Lemma A.1, printed p.28 (PDF 30), under the standing
lambda-exclusion assumption of printed p.27. General encoding matrices are allowed. -/
theorem lemma_A_1 {E U F : Type} [Field F] [Fintype F] [Fintype U]
    (z : U → ℕ) (G : E → Coord z → F) (W : Finset E)
    (htarget : target (F := F) z ∉ columnSpan G W)
    (y : W → F) (a b : F) :
    (affineIntersection G W a y).Nonempty ↔
      (affineIntersection G W b y).Nonempty := by sorry

end NetworkSumSecure.Solvability
