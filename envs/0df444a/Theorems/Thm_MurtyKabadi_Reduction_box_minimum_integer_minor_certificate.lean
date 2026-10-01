-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_box_minimum_integer_minor_certificate
-- name    : MurtyKabadi.Reduction.box_minimum_integer_minor_certificate
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T09:05:51.852211+00:00
-- url     : https://prove2.me/theorems/4179dbd0-af6f-40e0-b59a-d080438f6379
-- title:
--   A box minimum has a nonzero principal-minor denominator certificate
-- statement:
--   Let $D$ be a symmetric $m\times m$ integer matrix and let $Q(x)=x^{\mathsf T}Dx$. Suppose $x\in[0,1]^m$ is a global minimizer of $Q$ on this box. There are an index set $S\subseteq\{0,\ldots,m-1\}$ and an integer $a$ such that, with $k=\det D[S,S]$,
--
--   $$
--   k\ne 0,\qquad kQ(x)=a.
--   $$
--
--   This certificate identifies an integer denominator for the optimal value. Together with an encoding-size bound on principal minors, it gives the quantitative gap in Murty and Kabadi's Lemma 2. The empty principal minor has determinant $1$, so vertex minima and $m=0$ are included.
--
--   **Formalization Note** This is a principal-minor formulation of the denominator argument in the proof of Lemma 2, rather than a separately numbered statement in the paper. The chosen minimizer itself may have irrational coordinates; the certificate concerns its optimal value.
-- source:
--   K. G. Murty and S. N. Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Mathematical Programming 39 (1987), pp. 122-123, Lemma 2, program (8) and the denominator argument following (9)-(11). https://public.websites.umich.edu/~murty/np.pdf. Derived auxiliary formulation for this formalization, with the mission's existing encSize convention.

import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

open MurtyKabadi.Reduction

theorem MurtyKabadi.Reduction.box_minimum_integer_minor_certificate
    {m : ℕ} (D : Matrix (Fin m) (Fin m) ℤ) (hD : D.IsSymm)
    (x : Fin m → ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hmin : ∀ z : Fin m → ℝ, 0 ≤ z → z ≤ 1 →
      Q (D.map (Int.cast : ℤ → ℝ)) x ≤ Q (D.map (Int.cast : ℤ → ℝ)) z) :
    ∃ S : Finset (Fin m),
      (D.submatrix (fun i : S => i.1) (fun i : S => i.1)).det ≠ 0 ∧
      ∃ a : ℤ, Q (D.map (Int.cast : ℤ → ℝ)) x *
        ((D.submatrix (fun i : S => i.1) (fun i : S => i.1)).det : ℝ) = (a : ℝ) := by sorry
