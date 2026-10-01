-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_principal_minor_abs_le_encoding
-- name    : MurtyKabadi.Reduction.principal_minor_abs_le_encoding
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T09:06:21.109735+00:00
-- url     : https://prove2.me/theorems/9fd3073f-3d84-4bb4-a8a5-7772abb08742
-- title:
--   Every principal minor satisfies $|\det D[S,S]|\le 2^L$
-- statement:
--   Let $D$ be an $m\times m$ integer matrix, let $S\subseteq\{0,\ldots,m-1\}$, and define its encoding size by
--
--   $$
--   L=m^2+\sum_{i,j}\left(1+\left\lceil\log_2(|D_{ij}|+1)\right\rceil\right).
--   $$
--
--   Then its principal submatrix on $S$ satisfies
--
--   $$
--   |\det D[S,S]|\le 2^L.
--   $$
--
--   The bound controls the denominator in the optimal-value certificate used for Murty and Kabadi's Lemma 2. It applies without a symmetry assumption and includes the empty principal minor, whose determinant is $1$.
--
--   **Formalization Note** The formula for $L$ is the mission's existing `encSize` definition. This is an elementary auxiliary estimate for the paper's denominator-size argument, not a separately numbered theorem in the source.
-- source:
--   K. G. Murty and S. N. Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Mathematical Programming 39 (1987), pp. 122-123, Lemma 2, program (8) and the denominator argument following (9)-(11). https://public.websites.umich.edu/~murty/np.pdf. Derived auxiliary formulation for this formalization, with the mission's existing encSize convention.

import Definitions.Def_MurtyKabadi_Reduction_encSize

open MurtyKabadi.Reduction

theorem MurtyKabadi.Reduction.principal_minor_abs_le_encoding
    {m : ℕ} (D : Matrix (Fin m) (Fin m) ℤ) (S : Finset (Fin m)) :
    |(D.submatrix (fun i : S => i.1) (fun i : S => i.1)).det| ≤
      (2 : ℤ) ^ encSize D := by sorry
