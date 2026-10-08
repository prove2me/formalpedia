-- Prove2me | Theorems.Thm_Normal_champGen_normal
-- name    : Normal.champGen_normal
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T15:29:00.31797+00:00
-- url     : https://prove2.me/theorems/79771d27-eb83-4708-bfd3-281b7d421548
-- title:
--   Champernowne's Theorems I, II, IV in general form (base $b$, bounded repetition)
-- statement:
--   For $r\ge 1$ let $s_r$ denote the string obtained by writing all $b^r$ strings of $r$ base-$b$ digits in ascending order, $00\cdots0,\,00\cdots1,\,\dots,\,(b-1)\cdots(b-1)$ (so in base ten $s_2 = 00\,01\,02\cdots 99$).
--   Let $m:\mathbb N\to\mathbb N$ be a repetition schedule with $1\le m(r)\le K(r+1)$ for some constant $K$ and all $r\ge 0$, and let `champGen b m` be the digit sequence $({}_{m(0)}s_1)({}_{m(1)}s_2)({}_{m(2)}s_3)\cdots$, where ${}_{j}s_r$ is $s_r$ repeated $j$ times. **Theorem.** For $b\ge 2$ this digit sequence is normal in base $b$.
--
--   Here a digit sequence $s:\mathbb N\to\mathbb N$ is *normal in base $b$* (`IsNormalSeq b s`) if for every finite word $w=(w_0,\dots,w_{k-1})$ with all $w_j<b$, the number $\#\{i<N : s_{i+j}=w_j \text{ for all } j<k\}$ of (overlapping) occurrences of $w$ starting before position $N$ satisfies
--   $$\lim_{N\to\infty}\frac{\#\{i<N : s_{i}s_{i+1}\cdots s_{i+k-1}=w\}}{N}=b^{-k}.$$
--   A real number $x$ is normal in base $b$ (`IsNormalReal b x`) if its sequence of base-$b$ digits after the point, $d_n(x)=\lfloor x\,b^{n+1}\rfloor \bmod b$, is normal in base $b$. This is Borel normality as defined by Champernowne (p. 254) and Copeland–Erdős (p. 857).
--
--   Taking $m\equiv1$, $m\equiv\mu$ and $m(r)=r+1$ gives Champernowne's Theorems I, II and IV respectively, in every base. The proof applies the block criterion `Normal.isNormalSeq_flatten` with the members of the $s_r$ as blocks.
-- source:
--   D. G. Champernowne, The construction of decimals normal in the scale of ten, J. London Math. Soc. 8 (1933), 254–260, Theorems I, II, IV (p. 255), generalised. Lean source: https://github.com/xiangyazi24/normal/blob/ccb5977dc827e12f5f1b7266aec48a9b039370af/Normal/Champernowne.lean#L293-L454

import Init
import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false
set_option autoImplicit false
open Filter Topology
open Normal

theorem Normal.champGen_normal {b : ℕ} (hb : 2 ≤ b) {mult : ℕ → ℕ} (K : ℕ) (h1 : ∀ r, 1 ≤ mult r)
    (hK : ∀ r, mult r ≤ K * (r + 1)) : IsNormalSeq b (champGen b mult) := by sorry
