-- Prove2me | Theorems.Thm_IteratedFDeriv_exists_diagonal_tendstoUniformlyOn
-- name    : IteratedFDeriv.exists_diagonal_tendstoUniformlyOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T16:56:29.984768+00:00
-- url     : https://prove2.me/theorems/99451ed0-546c-408e-9e09-bfe66872b34c
-- title:
--   A diagonal subsequence of approximations of approximations converges in $C^\infty_{\mathrm{loc}}$
-- statement:
--   Let $E$ be a proper real normed space (e.g. $\mathbb{R}^n$) and $F$ a real normed space. Let $f:E\to F$, let $f_k:E\to F$ ($k\in\mathbb{N}$) satisfy $f_k\to f$ in $C^\infty_{\mathrm{loc}}$, and for each $k$ let $g_{k,j}:E\to F$ ($j\in\mathbb{N}$) satisfy $g_{k,j}\to f_k$ in $C^\infty_{\mathrm{loc}}$ as $j\to\infty$. Then there is $\varphi:\mathbb{N}\to\mathbb{N}$ with $g_{k,\varphi(k)}\to f$ in $C^\infty_{\mathrm{loc}}$ as $k\to\infty$.
--
--   Here $u_k\to u$ in $C^\infty_{\mathrm{loc}}$ means: for every $m\in\mathbb{N}$ and every compact $K\subset E$, the $m$-th Fréchet derivatives `iteratedFDeriv ℝ m u_k` converge to `iteratedFDeriv ℝ m u` uniformly on $K$. No smoothness of the functions is assumed. This is the step that combines two successive approximation procedures (first $f_k$, then $g_{k,j}$) into one approximating sequence of $f$.
-- source:
--   Standard (diagonal sequence for the Fréchet topology of $C^\infty_{\mathrm{loc}}$).

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.ProperSpace

theorem IteratedFDeriv.exists_diagonal_tendstoUniformlyOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (fk : ℕ → E → F) (g : ℕ → ℕ → E → F)
    (hf : ∀ m : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fk k)) (iteratedFDeriv ℝ m f) Filter.atTop K)
    (hg : ∀ k m : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (g k j)) (iteratedFDeriv ℝ m (fk k))
        Filter.atTop K) :
    ∃ φ : ℕ → ℕ, ∀ m : ℕ, ∀ K : Set E, IsCompact K →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (g k (φ k))) (iteratedFDeriv ℝ m f)
        Filter.atTop K := by sorry
