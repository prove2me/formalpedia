-- Prove2me | Theorems.Thm_LefebvreVariations_redheffer_det_eq_mertens
-- name    : LefebvreVariations.redheffer_det_eq_mertens
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:10:51.996156+00:00
-- url     : https://prove2.me/theorems/e78cf869-c535-4fd9-bd22-fe6acfd518d8
-- title:
--   Lefebvre's variations, No. 12 — on a theme by Redheffer: the Redheffer determinant equals the Mertens function
-- statement:
--   This is Redheffer's identity, the bridge between the Redheffer-matrix criterion for the Riemann Hypothesis and the Mertens function.
--
--   For $n\ge1$ let $A_n$ be the $n\times n$ Redheffer matrix, with entries $a_{ij}=1$ if $j=1$ or $i\mid j$, and $a_{ij}=0$ otherwise ($1\le i,j\le n$). Then
--
--   $$
--   \det A_n=\sum_{k=1}^{n}\mu(k)=M(n),
--   $$
--
--   where $\mu$ is the Möbius function and $M$ the Mertens function.
--
--   Combined with Littlewood's criterion ($M(n)=O(n^{1/2+\varepsilon})$ for every $\varepsilon>0$ is equivalent to the Riemann Hypothesis), this identity is what makes the growth of $\det A_n$ an equivalent form of the Riemann Hypothesis. It is unconditional.
--
--   **Formalization Note** Indices are $0$-based (`Fin n`), so $a_{ij}=1$ when $j=0$ or $(i+1)\mid(j+1)$; the matrix is defined inside the statement over $\mathbb R$.
-- source:
--   R. M. Redheffer, Eine explizit lösbare Optimierungsaufgabe, Internat. Schriftenreihe Numer. Math. 36 (1977), 213–216 (det A_n = M(n)); see also W. W. Barrett and T. J. Jarvis, Spectral properties of a matrix of Redheffer, Linear Algebra Appl. 162–164 (1992), 673–683, and K. Broughan, Equivalents of the Riemann Hypothesis, Vol. 1, Cambridge Univ. Press, 2017 (Redheffer's criterion). Parent problem: BroughanRH.redheffer.

import Mathlib

namespace LefebvreVariations

/-- Redheffer's identity (key lemma behind `BroughanRH.redheffer`): the determinant of the
Redheffer matrix `A_n` (`a_ij = 1` if `j = 1` or `i ∣ j`) is the Mertens function `M(n)`.
Redheffer (1977); Barrett–Jarvis, Linear Algebra Appl. 162–164 (1992); Vaughan (1993). -/
theorem redheffer_det_eq_mertens (n : ℕ) (hn : 1 ≤ n) :
    let A (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
      fun i j => if j.val = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0
    (A n).det = ∑ i ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius i : ℝ) := by
  sorry

end LefebvreVariations
