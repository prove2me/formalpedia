-- Prove2me | Theorems.Thm_Normal_champernowneConstant_normal
-- name    : Normal.champernowneConstant_normal
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T15:28:59.544095+00:00
-- url     : https://prove2.me/theorems/f89db4e4-6767-4399-bb0b-3a772e77e946
-- title:
--   The Champernowne constant is normal in every base $b\ge 2$
-- statement:
--   For an integer $b\ge 2$ let
--   $$C_b = 0.(1)_b(2)_b(3)_b(4)_b\cdots$$
--   be the real number whose base-$b$ expansion is obtained by writing the positive integers $1,2,3,\dots$ in base $b$ (most significant digit first, no leading zeros) one after another; for $b=10$ this is $0.123456789101112\ldots$. **Theorem.** $C_b$ is normal in base $b$.
--
--   Here a digit sequence $s:\mathbb N\to\mathbb N$ is *normal in base $b$* (`IsNormalSeq b s`) if for every finite word $w=(w_0,\dots,w_{k-1})$ with all $w_j<b$, the number $\#\{i<N : s_{i+j}=w_j \text{ for all } j<k\}$ of (overlapping) occurrences of $w$ starting before position $N$ satisfies
--   $$\lim_{N\to\infty}\frac{\#\{i<N : s_{i}s_{i+1}\cdots s_{i+k-1}=w\}}{N}=b^{-k}.$$
--   A real number $x$ is normal in base $b$ (`IsNormalReal b x`) if its sequence of base-$b$ digits after the point, $d_n(x)=\lfloor x\,b^{n+1}\rfloor \bmod b$, is normal in base $b$. This is Borel normality as defined by Champernowne (p. 254) and Copeland–Erdős (p. 857).
--
--   This is Champernowne's Theorem III, generalised from base ten to every base, and obtained (as Copeland and Erdős remark on p. 857) as a corollary of the Copeland–Erdős theorem applied to the sequence $a_n=n$.
-- source:
--   D. G. Champernowne, The construction of decimals normal in the scale of ten, J. London Math. Soc. 8 (1933), 254–260, Theorem III (p. 254); A. H. Copeland and P. Erdős, Note on normal numbers, Bull. Amer. Math. Soc. 52 (1946), 857–860, p. 857 (corollary). Lean source: https://github.com/xiangyazi24/normal/blob/ccb5977dc827e12f5f1b7266aec48a9b039370af/Normal/Main.lean#L26-L29

import Init
import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false
set_option autoImplicit false
open Filter Topology
open Normal

theorem Normal.champernowneConstant_normal {b : ℕ} (hb : 2 ≤ b) :
    IsNormalReal b (champernowneConstant b) := by sorry
