-- Prove2me | Theorems.Thm_JHolomorphic_contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv
-- name    : JHolomorphic.contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T15:34:41.376309+00:00
-- url     : https://prove2.me/theorems/974c1bc1-4bfa-43ee-9f81-a532573fa022
-- title:
--   Locally uniform limits of all derivatives of smooth maps are the derivatives of a smooth limit
-- statement:
--   Let $U$ be an open subset of a real normed space $X$ and $Y$ a real normed space. Let $f_\nu : X\to Y$ be $C^\infty$ on $U$, converging pointwise on $U$ to a map $v$, and suppose that for every $m\in\mathbb N$ the $m$-th derivatives $D^m f_\nu$ converge locally uniformly on $U$ to a map $g_m : X\to L^m(X;Y)$. Then $v$ is $C^\infty$ on $U$ and $D^m v = g_m$ on $U$ for every $m$.
--
--   Together with an extraction statement, this identifies limits of sequences converging in $C^\infty_{\mathrm{loc}}$.
--
--   **Formalization Note** $D^m$ is Mathlib's global `iteratedFDeriv ℝ m`; the conclusion is `ContDiffOn ℝ ∞ v U ∧ ∀ m, EqOn (iteratedFDeriv ℝ m v) (g m) U`.
-- source:
--   Elementary real analysis; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 9, Proposition 9.1

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

namespace JHolomorphic

open Metric Filter Topology Set
open scoped ContDiff

/-- Let `U` be an open subset of a real normed space `X`. Let maps `f ν : X → Y` be `C^∞` on `U`,
converging pointwise on `U` to `v`, and suppose that for every `m` the derivatives `Dᵐ (f ν)`
converge locally uniformly on `U` to some `g m`. Then `v` is `C^∞` on `U` and `Dᵐ v = g m` on `U`
for every `m`. -/
theorem contDiffOn_of_tendstoLocallyUniformlyOn_iteratedFDeriv
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U : Set X} (hU : IsOpen U) (f : ℕ → X → Y) (hf : ∀ ν, ContDiffOn ℝ ∞ (f ν) U)
    (v : X → Y) (hv : ∀ x ∈ U, Tendsto (fun ν => f ν x) atTop (𝓝 (v x)))
    (g : (m : ℕ) → X → ContinuousMultilinearMap ℝ (fun _ : Fin m => X) Y)
    (hg : ∀ m, TendstoLocallyUniformlyOn (fun ν => iteratedFDeriv ℝ m (f ν)) (g m) atTop U) :
    ContDiffOn ℝ ∞ v U ∧ ∀ m, EqOn (iteratedFDeriv ℝ m v) (g m) U := by
  sorry

end JHolomorphic
