-- Prove2me | Theorems.Thm_Normal_copeland_erdos
-- name    : Normal.copeland_erdos
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T15:29:22.260971+00:00
-- url     : https://prove2.me/theorems/07d4c5ee-1a04-4725-b654-b2e94a485d16
-- title:
--   Theorem of Copeland–Erdős: dense increasing sequences give normal numbers
-- statement:
--   Let $b\ge2$ and let $a_0<a_1<a_2<\cdots$ be a strictly increasing sequence of positive integers which is *dense* in the sense that for every $\theta<1$,
--   $$\#\{i : a_i\le N\} > N^{\theta}\qquad\text{for all sufficiently large } N$$
--   (formally, the count is taken over $i\le N$, which loses nothing since $a_i\ge i$). Let `concatDigits b a` be the digit sequence obtained by writing $a_0,a_1,a_2,\dots$ in base $b$ (most significant digit first) one after another. **Theorem.** This digit sequence is normal in base $b$; equivalently the real number $0.(a_0)_b(a_1)_b(a_2)_b\cdots$ is normal in base $b$.
--
--   Here a digit sequence $s:\mathbb N\to\mathbb N$ is *normal in base $b$* (`IsNormalSeq b s`) if for every finite word $w=(w_0,\dots,w_{k-1})$ with all $w_j<b$, the number $\#\{i<N : s_{i+j}=w_j \text{ for all } j<k\}$ of (overlapping) occurrences of $w$ starting before position $N$ satisfies
--   $$\lim_{N\to\infty}\frac{\#\{i<N : s_{i}s_{i+1}\cdots s_{i+k-1}=w\}}{N}=b^{-k}.$$
--   A real number $x$ is normal in base $b$ (`IsNormalReal b x`) if its sequence of base-$b$ digits after the point, $d_n(x)=\lfloor x\,b^{n+1}\rfloor \bmod b$, is normal in base $b$. This is Borel normality as defined by Champernowne (p. 254) and Copeland–Erdős (p. 857).
--
--   This is the main theorem of Copeland and Erdős (1946). The proof combines the large-deviation lemma `Normal.large_deviation` with the block criterion `Normal.isNormalSeq_flatten`.
-- source:
--   A. H. Copeland and P. Erdős, Note on normal numbers, Bull. Amer. Math. Soc. 52 (1946), 857–860, Theorem (p. 857); proof pp. 858–860. Lean source: https://github.com/xiangyazi24/normal/blob/ccb5977dc827e12f5f1b7266aec48a9b039370af/Normal/CopelandErdos.lean#L435-L445

import Init
import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false
set_option autoImplicit false
open Filter Topology
open Normal

theorem Normal.copeland_erdos {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a) (ha0 : 0 < a 0)
    (hdense : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ < (((Finset.range (N + 1)).filter (fun i => a i ≤ N)).card : ℝ)) :
    IsNormalSeq b (concatDigits b a) := by sorry
