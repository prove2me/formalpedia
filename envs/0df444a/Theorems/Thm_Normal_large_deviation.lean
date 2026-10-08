-- Prove2me | Theorems.Thm_Normal_large_deviation
-- name    : Normal.large_deviation
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T15:29:29.926212+00:00
-- url     : https://prove2.me/theorems/6049c216-bd1e-41be-815b-5fdf621235c0
-- title:
--   Copeland–Erdős Lemma: few words have too many occurrences of a given block
-- statement:
--   Let $b\ge2$, let $w$ be a nonempty word over $\{0,\dots,b-1\}$ of length $k$, and let $\varepsilon>0$. **Theorem.** There are real constants $0\le\beta<b$ and $C$ such that for every $n$, the number of words $u$ of length $n$ over $\{0,\dots,b-1\}$ in which $w$ occurs (with overlaps) more than $(b^{-k}+\varepsilon)\,n$ times is at most
--   $$C\,\beta^{\,n}.$$
--   In other words, words in which $w$ is over-represented form an *exponentially thin* family. This is the lemma on p. 858 of Copeland–Erdős (stated there for integers up to $N$), proved here by a Chernoff exponential-moment bound on the occurrences in each residue class of positions modulo $k$.
-- source:
--   A. H. Copeland and P. Erdős, Note on normal numbers, Bull. Amer. Math. Soc. 52 (1946), 857–860, Lemma (p. 858). Lean source: https://github.com/xiangyazi24/normal/blob/ccb5977dc827e12f5f1b7266aec48a9b039370af/Normal/LargeDeviation.lean#L244-L319

import Init
import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false
set_option autoImplicit false
open Filter Topology
open Normal

theorem Normal.large_deviation {b : ℕ} (hb : 2 ≤ b) {w : List ℕ} (hw : w ≠ [])
    (hwd : ∀ d ∈ w, d < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 ≤ β ∧ β < b ∧ ∃ C : ℝ, ∀ n : ℕ,
      (((strs b n).filter
          (fun u => (((b : ℝ) ^ w.length)⁻¹ + ε) * u.length < occ w u)).card : ℝ)
        ≤ C * β ^ n := by sorry
