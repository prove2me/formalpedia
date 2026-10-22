-- Prove2me | Theorems.Thm_JHolomorphic_exists_norm_le_of_eLpNorm_fderiv_le
-- name    : JHolomorphic.exists_norm_le_of_eLpNorm_fderiv_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T22:25:37.758993+00:00
-- url     : https://prove2.me/theorems/661e57b0-d885-449e-a4fc-4d60328f49c9
-- title:
--   Uniform local sup bounds from uniform local $W^{1,p}$ bounds in the plane, $p>2$
-- statement:
--   Let $F$ be a real Banach space, $U\subseteq\mathbb{C}$ open and $p>2$. Let $f_\nu:U\to F$ ($\nu\in\mathbb{N}$) be $C^1$ maps such that for every compact $K\subseteq U$
--   $$\sup_\nu\bigl(\|f_\nu\|_{L^p(K)}+\|Df_\nu\|_{L^p(K)}\bigr)<\infty.$$
--   Then for every compact $K\subseteq U$ there is $M$ with $\|f_\nu(z)\|\le M$ for all $\nu$ and all $z\in K$. This is the uniform, local form of the embedding $W^{1,p}\subset L^\infty$ in two dimensions for $p>2$.
--
--   **Formalization Note** The maps are `f : ℕ → ℂ → F` with `ContDiffOn ℝ 1 (f ν) U` and `[CompleteSpace F]`. The hypothesis gives, for each compact `K ⊆ U`, one `C : ℝ≥0` with `eLpNorm (f ν) (ENNReal.ofReal p) (volume.restrict K) ≤ C` and `eLpNorm (fderiv ℝ (f ν)) (ENNReal.ofReal p) (volume.restrict K) ≤ C` for all `ν`; the derivative is measured in operator norm. The constant `M` depends on `K` and is chosen before `ν`.
-- source:
--   Morrey's inequality; see L. C. Evans, Partial Differential Equations, §5.6.2, and D. Gilbarg, N. Trudinger, Elliptic PDE of Second Order, Theorem 7.17

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

/-- Uniform local sup bounds from uniform local `W^{1,p}` bounds, `p > 2`: let `f_ν` be `C¹`
maps on an open set `U ⊆ ℂ` with values in a complete real normed space. If on every compact
`K ⊆ U` the norms `‖f_ν‖_{L^p(K)}` and `‖Df_ν‖_{L^p(K)}` are bounded uniformly in `ν`, then on
every compact `K ⊆ U` the values `‖f_ν(z)‖` are bounded uniformly in `ν` and `z ∈ K`. -/
theorem exists_norm_le_of_eLpNorm_fderiv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (p : ℝ) (hp : 2 < p) (U : Set ℂ) (hU : IsOpen U) (f : ℕ → ℂ → F)
    (hf : ∀ ν, ContDiffOn ℝ 1 (f ν) U)
    (hbd : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0, ∀ ν,
      eLpNorm (f ν) (ENNReal.ofReal p) (volume.restrict K) ≤ C ∧
        eLpNorm (fderiv ℝ (f ν)) (ENNReal.ofReal p) (volume.restrict K) ≤ C) :
    ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ ν, ∀ z ∈ K, ‖f ν z‖ ≤ M := by
  sorry

end JHolomorphic
