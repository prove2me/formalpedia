-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_theorem_12
-- name    : LogBarrierIPM.Iterations.Supplement.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:15:59.366979+00:00
-- url     : https://prove2.me/theorems/aa3499ba-2d1c-4222-9fa1-10431c3bc265
-- title:
--   Theorem 12 — explicit monomial bound (corrected: vertex specialization, or nonempty with sign rows)
-- statement:
--   Let $d\ge1$, let $\mathcal P=\{x\in K^d:Ax\le b\}\subseteq K_+^d$ have monomial data, and let $\eta_0$ be the minimum exponent gap over all order-$d$ submatrices of $(A\ b\ 0;\ e^\top\ 0\ 1)$. Suppose $t>1$, $t\ge(d!)^{1/\eta_0}$, and that at least one of the following holds:
--
--   1. $\mathcal P(t)$ is contained in the convex hull of the evaluated vertices of $\mathcal P$ plus the cone of the evaluated vertices of $\{v:Av\le0,\ e^\top v=1\}$;
--   2. $\mathcal P$ is nonempty and each inequality $-x_j\le0$ is a row of $Ax\le b$.
--
--   Then
--   $$d_H(\log_t\mathcal P(t),\operatorname{val}(\mathcal P))\le\log_t\bigl((d+1)^2(d!)^4\bigr).$$
--   The threshold and constant are those of the paper. The printed theorem, with neither condition, is false: for the rows $-x_1+x_3\le1$, $x_2-x_3\le1$, $x_1-x_2+x_3\le1$, $x_1+x_2+x_3\ge t$ and $x\ge0$, one has $\eta_0=1$ and $\mathcal P=\emptyset$, while at $t=7>6$ the point $(14/9,28/9,7/3)$ lies in $\mathcal P(7)$, so the distance is $+\infty$.
--
--   Differences from the source:
--   - correction: the explicit threshold alone ensures the bound → the same threshold and constant, assuming VertexCoverAt at the chosen t, or that P is nonempty and contains the rows -x_j ≤ 0; reason: the proof applies (16), which needs P(t) inside the hull and cone of the evaluated generators, and Proposition 3 gives this only eventually; the d=3, t=7 example refutes the printed claim; with P nonempty and sign rows the bound follows at the printed threshold by linear-programming duality
--   - encoding: base-t logarithmic inequalities and infinite exponent gaps → t>1 and reciprocal of +∞ equal to zero; reason: excludes bases at which the displayed logarithmic inequality is undefined or reversed; this is the convention of (13) and the published Lemma 11
--   - encoding: directed distance between subsets of T^d → an extended-real distance with empty-source value 0 and empty-target value +∞; reason: empty polyhedra are allowed by (9)
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
--   - encoding: vectors indexed from 1 → 0-based Fin vectors; reason: the index shift preserves every coordinate
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 13, Theorem 12

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_MonomialPolyhedron

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem theorem_12 {p d : ℕ} (hd : 1 ≤ d)
    (A : Matrix (Fin p) (Fin d) Puiseux) (b : Fin p → Puiseux)
    (a : Matrix (Fin p) (Fin d) (WithBot ℝ)) (β : Fin p → WithBot ℝ)
    (s : Matrix (Fin p) (Fin d) ℝ) (σ : Fin p → ℝ)
    (hA : ∀ i j, IsMonomial (A i j) (a i j) (s i j))
    (hb : ∀ i, IsMonomial (b i) (β i) (σ i))
    (horthant : kOrthant (kPolyhedron A b))
    (t : ℝ) (ht : 1 < t) (hthreshold : monomialThreshold a β ≤ t)
    (hrepair : VertexCoverAt A b t ∨
      ((kPolyhedron A b).Nonempty ∧ HasNonnegativityRows A b)) :
    hausdorffH (logImage t (realPolyhedron A b t)) (valVec '' kPolyhedron A b) ≤
      (Real.logb t (((d + 1 : ℕ) : ℝ) ^ 2 * (Nat.factorial d : ℝ) ^ 4) : EReal) := by sorry

end LogBarrierIPM.Iterations.Supplement
