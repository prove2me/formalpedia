-- Prove2me | Theorems.Thm_MulticlassDS_Compress_lemma40_menu_compression
-- name    : MulticlassDS.Compress.lemma40_menu_compression
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:03:55.93377+00:00
-- url     : https://prove2.me/theorems/07aacce1-9689-4074-98ae-9da92a0e731f
-- title:
--   Lemma 40, p. 23 — an n → r₂ sample compression scheme for H and a p-menu with r₂ ≤ 10³ d_N log(p) log(2n)
-- statement:
--   Let $\mathcal H\subseteq\mathcal Y^{\mathcal X}$ have Natarajan dimension $d_N<\infty$ and let $\mu$ be a $p$-menu. For every integer $n>0$ there is an $n\to r_2$ sample compression scheme for $\mathcal H$ and $\mu$ with
--   $$r_2\ \le\ 10^3\,d_N\log(p)\log(2n),$$
--   logarithms in base $2$.
--
--   This is the second component of the compression scheme of Theorem 36: once a menu is known, a further short subsample pins down the labels.
--
--   **Formalization Note** Logarithms are `Real.logb 2`. The label set is assumed non-empty: when $d_N = 0$ the bound is $0$, so the reconstruction function must output a hypothesis from the empty subsample, and if $\mathcal X\neq\emptyset$ and $\mathcal Y=\emptyset$ no function $\mathcal X\to\mathcal Y$ exists; the paper's label sets are non-empty. At $p\le1$ or $d_N = 0$ the bound is $0$ and $r_2 = 0$ suffices ($p = 0$: no menu-realizable sample exists; $p = 1$: the menu determines every label; $d_N = 0$: $|\mathcal H|\le1$).
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 23, Lemma 40

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Compression

namespace MulticlassDS.Compress

theorem lemma40_menu_compression {X Y : Type*} [Nonempty Y] (H : Set (X → Y)) (dN : ℕ)
    (hN : natarajanDim H = dN) (μ : X → Set Y) (p : ℕ) (hμ : IsMenu μ p) (n : ℕ) (hn : 0 < n) :
    ∃ r₂ : ℕ, (r₂ : ℝ) ≤ 10 ^ 3 * dN * Real.logb 2 p * Real.logb 2 (2 * (n : ℝ)) ∧
      ∃ ρ : (Fin r₂ → X × Y) → X → Y, IsMenuCompressionScheme H μ n r₂ ρ := by sorry

end MulticlassDS.Compress
