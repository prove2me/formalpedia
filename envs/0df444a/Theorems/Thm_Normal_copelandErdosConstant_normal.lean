-- Prove2me | Theorems.Thm_Normal_copelandErdosConstant_normal
-- name    : Normal.copelandErdosConstant_normal
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T15:29:10.057879+00:00
-- url     : https://prove2.me/theorems/0d7ee62f-cf89-4000-afa0-3868b5865085
-- title:
--   The Copeland–Erdős constant is normal in every base $b\ge 2$
-- statement:
--   For an integer $b\ge 2$ let
--   $$E_b = 0.(2)_b(3)_b(5)_b(7)_b(11)_b\cdots$$
--   be the real number whose base-$b$ expansion is the concatenation of the base-$b$ expansions of the primes $p_1=2<p_2=3<p_3=5<\cdots$ in increasing order; for $b=10$ this is $0.235711131719\ldots$. **Theorem.** $E_b$ is normal in base $b$.
--
--   Here a digit sequence $s:\mathbb N\to\mathbb N$ is *normal in base $b$* (`IsNormalSeq b s`) if for every finite word $w=(w_0,\dots,w_{k-1})$ with all $w_j<b$, the number $\#\{i<N : s_{i+j}=w_j \text{ for all } j<k\}$ of (overlapping) occurrences of $w$ starting before position $N$ satisfies
--   $$\lim_{N\to\infty}\frac{\#\{i<N : s_{i}s_{i+1}\cdots s_{i+k-1}=w\}}{N}=b^{-k}.$$
--   A real number $x$ is normal in base $b$ (`IsNormalReal b x`) if its sequence of base-$b$ digits after the point, $d_n(x)=\lfloor x\,b^{n+1}\rfloor \bmod b$, is normal in base $b$. This is Borel normality as defined by Champernowne (p. 254) and Copeland–Erdős (p. 857).
--
--   This settles Champernowne's conjecture; it is the main corollary of the theorem of Copeland and Erdős, using Chebyshev's lower bound $\pi(N)>N^{\theta}$ (for every $\theta<1$ and all large $N$).
-- source:
--   A. H. Copeland and P. Erdős, Note on normal numbers, Bull. Amer. Math. Soc. 52 (1946), 857–860, p. 857 (Champernowne's conjecture). Lean source: https://github.com/xiangyazi24/normal/blob/ccb5977dc827e12f5f1b7266aec48a9b039370af/Normal/Main.lean#L31-L35

import Init
import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false
set_option autoImplicit false
open Filter Topology
open Normal

theorem Normal.copelandErdosConstant_normal {b : ℕ} (hb : 2 ≤ b) :
    IsNormalReal b (copelandErdosConstant b) := by sorry
