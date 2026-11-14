-- Prove2me | Theorems.Thm_LatticePrepro_radius_bound_gt_two
-- name    : LatticePrepro.radius_bound_gt_two
-- status  : Proved
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:26:02.687951+00:00
-- url     : https://prove2.me/theorems/a16c7ae5-7a6c-4f9b-87b4-743060d825e0
-- title:
--   Radius bound for $2<p<\infty$ (proof of Lemma 3.12, eq. (43))
-- statement:
--   Let $q,t,D,A,B,w$ be real numbers with
--   $$q>2,\qquad t\ge1,\qquad D\ge1,\qquad B\ge0,\qquad w\le\frac{A}{t},\qquad A\le(2tD)^{1-2/q}\,B^{2/q}.$$
--   Then
--   $$w\le16\,D\,\Biggl(\frac{B^{1/q}}{\bigl\lceil(tD)^{1/q}\bigr\rceil}\Biggr)^{2},$$
--   where $\lceil\cdot\rceil$ is the ceiling, a natural number read in $\mathbb R$.
--
--   This is the real-number estimate behind the weight bound (43) in the proof of Lemma 3.12 for $2<p<\infty$. There $q=p$, $t=2^k$ is the padded block size, $D$ the number of blocks, $M=2tD$ the lattice dimension, $B=\sum_i|r_i|^p$ for the residual $r=t_x-v$ (so $B^{1/p}=\|r\|_p$), $A=\|r\|_2^2$, and $w$ is the residual weight. The hypotheses are the Parseval bound $w\le\|r\|_2^2/t$ of (42) and the power-mean inequality $\|r\|_2^2\le M^{1-2/p}\|r\|_p^2$. The conclusion is $w\le16D(\|r\|_p/R)^2$ for the radius $R=\lceil(tD)^{1/p}\rceil$, which is the weight bound of Lemma 3.12 with $s=2$.
--
--   **Formalization Note.** All powers with exponents $1-2/q$, $2/q$, $1/q$ and the outer exponent $2$ are real powers (`Real.rpow`); the ceiling is `Nat.ceil`.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), auxiliary lemma used in the proof of Lemma 3.12 (\label{lem:block-system-lattices}), equation (43) (\label{eq:residue-weight}) for 2 < p < ∞; Lean: LatticePrepro/Conversions/Lattices.lean, LatticePrepro.radius_bound_gt_two

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices

open LatticePrepro

theorem LatticePrepro.radius_bound_gt_two {q t D A B w : ℝ} (hq : 2 < q) (ht : 1 ≤ t) (hD : 1 ≤ D)
    (hB : 0 ≤ B) (hw : w ≤ A / t) (hAB : A ≤ (2 * (t * D)) ^ (1 - 2 / q) * B ^ (2 / q)) :
    w ≤ 16 * D * (B ^ (1 / q) / (⌈(t * D) ^ (1 / q)⌉₊ : ℝ)) ^ (2 : ℝ) := by sorry
