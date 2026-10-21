-- Prove2me | Theorems.Thm_JHolomorphic_bounded_iteratedFDeriv_of_sobolevNorm_le
-- name    : JHolomorphic.bounded_iteratedFDeriv_of_sobolevNorm_le
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T20:31:47.494427+00:00
-- url     : https://prove2.me/theorems/34095e23-1ff1-4b46-a688-61f94f639c3b
-- title:
--   Uniform interior $C^m$ bounds for $W^{1,p}$-bounded pseudoholomorphic maps
-- statement:
--   Let $E$ be a finite-dimensional real vector space, $O\subseteq E$ open, and let $J_\nu$, $J$ be smooth almost complex structures on $O$ with $J_\nu\to J$ in $C^\infty_{\mathrm{loc}}$ on $O$. Let $K_0\subseteq O$ be compact and let $D\subset\mathbb{C}$ be the open unit disc. Let $p>2$ and let $u_\nu:D\to K_0$ be $C^\infty$ maps with $\partial_su_\nu+J_\nu(u_\nu)\,\partial_tu_\nu=0$ on $D$ and
--   $$\sup_\nu\|u_\nu\|_{W^{1,p}(D)}<\infty.$$
--   Then for every compact $K\subset D$ and every $m\ge0$ there is $M$ with $\|D^mu_\nu(z)\|\le M$ for all $\nu$ and all $z\in K$.
--
--   **Formalization Note** The hypotheses on the structures are `IsAlmostComplexOn J O`, `∀ ν, IsAlmostComplexOn (Jν ν) O` and `TendstoCInftyLocOn Jν J O`. Because $J$ is only defined on $O$, the maps are required to take values in the fixed compact set $K_0\subseteq O$ (`Set.MapsTo (u ν) (ball 0 1) K₀`). The $W^{1,p}$ bound is `sobolevNorm 1 (ENNReal.ofReal p) (ball 0 1) (u ν) ≤ C` with `C : ℝ≥0`. The constant $M$ depends on $K$ and $m$ and is chosen before $\nu$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, Theorem 2.22 (2a), p. 35 (case k = 1)

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

/-- Wendl, Theorem 2.22 (2a) (p. 35), case `k = 1`: let `p > 2` and let `J_ν → J` in `C^∞_loc`
be smooth almost complex structures on an open set `O ⊆ E`. If smooth `J_ν`-holomorphic maps
`u_ν` on the open unit disc, with values in a fixed compact `K₀ ⊆ O`, are uniformly bounded in
`W^{1,p}`, then on every compact subset of the disc every derivative `Dᵐ u_ν` is bounded
uniformly in `ν`. (Wendl takes `E = O = ℂⁿ`, where the `W^{1,p}` bound already confines the
images to a compact set.) -/
theorem bounded_iteratedFDeriv_of_sobolevNorm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ ∞ (u ν) (ball 0 1))
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) (ball 0 1) (u ν))
    (hmaps : ∀ ν, Set.MapsTo (u ν) (ball 0 1) K₀) (C : ℝ≥0)
    (hC : ∀ ν, sobolevNorm 1 (ENNReal.ofReal p) (ball 0 1) (u ν) ≤ C) :
    ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K → ∀ m : ℕ,
      ∃ M : ℝ, ∀ ν, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (u ν) z‖ ≤ M := by
  sorry

end JHolomorphic
