-- Prove2me | Theorems.Thm_JHolomorphic_exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv
-- name    : JHolomorphic.exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T15:34:41.57182+00:00
-- url     : https://prove2.me/theorems/706409bf-af82-47f6-ac53-27363af99cf5
-- title:
--   Smooth maps with locally uniformly bounded derivatives of all orders have a subsequence whose derivatives all converge locally uniformly
-- statement:
--   Let $U$ be an open subset of a finite-dimensional real normed space $X$, and let $Y$ be a finite-dimensional real normed space. Let $f_\nu : X\to Y$ ($\nu\in\mathbb N$) be maps that are $C^\infty$ on $U$ and such that for every compact $K\subseteq U$ and every $m\in\mathbb N$
--   $$\sup_\nu\sup_{x\in K}\|D^m f_\nu(x)\|<\infty .$$
--   Then there are a strictly increasing $\varphi:\mathbb N\to\mathbb N$ and maps $g_m : X\to L^m(X;Y)$ (continuous $m$-linear maps), $m\in\mathbb N$, such that for every $m$ the derivatives $D^m f_{\varphi(\nu)}$ converge to $g_m$ locally uniformly on $U$.
--
--   This is the extraction step of compactness results for sequences of smooth maps with locally bounded derivatives of all orders (e.g. $C^\infty_{\mathrm{loc}}$ compactness of pseudoholomorphic curves).
--
--   **Formalization Note** $D^m$ is Mathlib's global `iteratedFDeriv ℝ m`, and the conclusion is `TendstoLocallyUniformlyOn (fun ν => iteratedFDeriv ℝ m (f (φ ν))) (g m) atTop U` for every `m`. The maps $g_m$ are only constrained on $U$.
-- source:
--   Elementary real analysis; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 9, Proposition 9.1

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

namespace JHolomorphic

open Metric Filter Topology Set
open scoped ContDiff

/-- Let `U` be an open subset of a finite-dimensional real normed space `X` and let `Y` be a
finite-dimensional real normed space. If maps `f ν : X → Y` are `C^∞` on `U` and, on every compact
`K ⊆ U`, each derivative `Dᵐ (f ν)` is bounded uniformly in `ν`, then some subsequence `f ∘ φ` has
every derivative `Dᵐ (f (φ ν))` converging locally uniformly on `U`. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_iteratedFDeriv
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {U : Set X} (hU : IsOpen U) (f : ℕ → X → Y) (hf : ∀ ν, ContDiffOn ℝ ∞ (f ν) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∀ m : ℕ, ∃ M : ℝ, ∀ ν, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (f ν) x‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : (m : ℕ) → X → ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Y,
        ∀ m, TendstoLocallyUniformlyOn (fun ν => iteratedFDeriv ℝ m (f (φ ν))) (g m) atTop U := by
  sorry

end JHolomorphic
