-- Prove2me | Theorems.Thm_LineVsPoint_lemma_3_2
-- name    : LineVsPoint.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:04:03.661273+00:00
-- url     : https://prove2.me/theorems/ce21e306-fdc6-4919-9d95-7cfd7105ff22
-- title:
--   Lemma 3.2 — a squarefree interpolant of weighted degree at most $D$
-- statement:
--   **Lemma 3.2.** Let $\mathbb F_q$ be a finite field, $d\ge1$, $f:\mathbb F_q^2\to\mathbb F_q$ a point table and $D=\lceil 4(dq^2)^{1/3}\rceil$. There is a nonzero squarefree polynomial $A\in\mathbb F_q[X,Y,Z]$ with $\mathrm{wdeg}(A)\le D$ such that
--
--   $$
--   A(x,f(x))=0\qquad\forall x\in\mathbb F_q^2 .
--   $$
--
--   The weighted degree uses the weights $1,1,d$ on $X,Y,Z$. The interpolant $A$ vanishes on the graph of $f$ and, by its degree, identically on every line with more than $D$ accepted points; it is the polynomial relation that Section 3 transfers to the line polynomials.
--
--   Differences from the source:
--   - generalization: under the Section 3 context Acc(f, {P_L}) ≥ ε ≥ C(d/q)^{1/3} → for every point table f : F² → F and every d ≥ 1, with no acceptance hypothesis; reason: the proof uses only dim V_D > D³/(6d) ≥ 64q²/6 > q²; the paper's statement is the special case
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), Lemma 3.2, p.15

import Definitions.Def_LineVsPoint_sec3D

set_option autoImplicit false

universe u

namespace LineVsPoint

open MvPolynomial in
/-- **Lemma 3.2** (squarefree interpolant). *There is a nonzero squarefree polynomial
`A ∈ F_q[X, Y, Z]` with `wdeg(A) ≤ D` such that `A(x, f(x)) = 0 ∀x ∈ F²_q`.*
Here `D = ⌈4(dq²)^{1/3}⌉` (§3, p.15). Dao, Kominers, Thaler, Zheng, *Cube-Root Soundness Is
Optimal for the Line–versus–Point Test* (manuscript, sha256 328a8943…), Lemma 3.2, p.15.

**Formalization Note.** `wdeg` has weights `1, 1, d` on `X, Y, Z` (§2.3, p.11). The statement is
for every point table `f : F² → F` and every `d ≥ 1`, without the Section 3 acceptance
hypothesis, which the lemma's proof does not use. -/
theorem lemma_3_2 :
    ∀ (F : Type u) [Field F] [Fintype F] (d : ℕ), 1 ≤ d → ∀ f : (Fin 2 → F) → F,
      ∃ A : MvPolynomial (Fin 3) F, A ≠ 0 ∧ Squarefree A ∧
        weightedTotalDegree ![1, 1, d] A ≤ sec3D d (Fintype.card F) ∧
        ∀ x : Fin 2 → F, eval ![x 0, x 1, f x] A = 0 := by sorry

end LineVsPoint
