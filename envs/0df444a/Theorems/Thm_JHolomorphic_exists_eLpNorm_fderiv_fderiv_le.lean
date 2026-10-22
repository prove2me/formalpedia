-- Prove2me | Theorems.Thm_JHolomorphic_exists_eLpNorm_fderiv_fderiv_le
-- name    : JHolomorphic.exists_eLpNorm_fderiv_fderiv_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T22:25:38.498995+00:00
-- url     : https://prove2.me/theorems/d6683678-1d78-4fa9-b498-43fc77a47fc3
-- title:
--   Uniform interior $W^{2,p}$ bounds for pseudoholomorphic maps with locally bounded $W^{1,p}$ norms
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $O\subseteq E$ open, and let $J_\nu$, $J$ be smooth almost complex structures on $O$ with $J_\nu\to J$ in $C^\infty_{\mathrm{loc}}$ on $O$. Let $K_0\subseteq O$ be compact, $U\subseteq\mathbb{C}$ open and $p>2$. Let $u_\nu:U\to K_0$ be $C^\infty$ maps with $\partial_su_\nu+J_\nu(u_\nu)\,\partial_tu_\nu=0$ on $U$ such that for every compact $K\subseteq U$
--   $$\sup_\nu\|Du_\nu\|_{L^p(K)}<\infty.$$
--   Then for every compact $K\subseteq U$
--   $$\sup_\nu\|D^2u_\nu\|_{L^p(K)}<\infty.$$
--   This is the interior $W^{2,p}$ part of the uniform regularity statement for sequences of pseudoholomorphic maps; it is used to bound the first derivatives of such sequences uniformly on compact sets.
--
--   **Formalization Note** The structures satisfy `IsAlmostComplexOn J O`, `∀ ν, IsAlmostComplexOn (Jν ν) O` and `TendstoCInftyLocOn Jν J O`; the maps satisfy `ContDiffOn ℝ ∞ (u ν) U`, `IsJHolomorphicOn (Jν ν) U (u ν)` and `Set.MapsTo (u ν) U K₀`. The norms are `eLpNorm (fderiv ℝ (u ν)) (ENNReal.ofReal p) (volume.restrict K)` and `eLpNorm (fderiv ℝ (fderiv ℝ (u ν))) (ENNReal.ofReal p) (volume.restrict K)`, in operator norm, bounded by a constant `C : ℝ≥0` chosen for each compact `K` before `ν`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, Theorem 2.22 (2a), p. 35 (the case k = 1, interior W^{2,p} part)

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

/-- Uniform interior `L^p` bounds on second derivatives (Wendl, Lecture 2, Theorem 2.22 (2a) with
`k = 1`, the `W^{2,p}_loc` part): let `p > 2` and let `J_ν → J` in `C^∞_loc` be smooth almost
complex structures on an open set `O ⊆ E`. Let `u_ν` be smooth `J_ν`-holomorphic maps on an open set
`U ⊆ ℂ` with values in a fixed compact `K₀ ⊆ O`, such that on every compact `K ⊆ U` the norms
`‖Du_ν‖_{L^p(K)}` are bounded uniformly in `ν`. Then on every compact `K ⊆ U` the norms
`‖D²u_ν‖_{L^p(K)}` are bounded uniformly in `ν`. -/
theorem exists_eLpNorm_fderiv_fderiv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (U : Set ℂ) (hU : IsOpen U) (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ ∞ (u ν) U)
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) U (u ν)) (hmaps : ∀ ν, Set.MapsTo (u ν) U K₀)
    (hbd : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ ν,
      eLpNorm (fderiv ℝ (u ν)) (ENNReal.ofReal p) (volume.restrict K) ≤ C) :
    ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ ν,
      eLpNorm (fderiv ℝ (fderiv ℝ (u ν))) (ENNReal.ofReal p) (volume.restrict K) ≤ C := by
  sorry

end JHolomorphic
