-- Prove2me | Theorems.Thm_JHolomorphic_tendstoCInftyLocOn_of_sobolevNorm_tendsto
-- name    : JHolomorphic.tendstoCInftyLocOn_of_sobolevNorm_tendsto
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T20:32:04.259302+00:00
-- url     : https://prove2.me/theorems/5211411d-2dbc-4952-9b4a-f5989337c4e7
-- title:
--   Pseudoholomorphic maps converging in $W^{1,p}$ converge in $C^\infty_{\mathrm{loc}}$
-- statement:
--   Let $E$ be a finite-dimensional real vector space, $O\subseteq E$ open, and let $J_\nu$, $J$ be smooth almost complex structures on $O$ with $J_\nu\to J$ in $C^\infty_{\mathrm{loc}}$ on $O$. Let $K_0\subseteq O$ be compact and let $D\subset\mathbb{C}$ be the open unit disc. Let $p>2$, let $u_\nu:D\to K_0$ be $C^\infty$ maps with $\partial_su_\nu+J_\nu(u_\nu)\,\partial_tu_\nu=0$ on $D$, and let $v$ be $C^\infty$ on $D$. If $\|u_\nu-v\|_{W^{1,p}(D)}\to0$, then $u_\nu\to v$ in $C^\infty_{\mathrm{loc}}$ on $D$.
--
--   **Formalization Note** The hypotheses on the structures are `IsAlmostComplexOn J O`, `∀ ν, IsAlmostComplexOn (Jν ν) O` and `TendstoCInftyLocOn Jν J O`. Because $J$ is only defined on $O$, the maps are required to take values in the fixed compact set $K_0\subseteq O$ (`Set.MapsTo (u ν) (ball 0 1) K₀`). The convergence hypothesis is `Tendsto (fun ν => sobolevNorm 1 (ENNReal.ofReal p) (ball 0 1) (u ν - v)) atTop (𝓝 0)`; the conclusion is `TendstoCInftyLocOn u v (ball 0 1)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, Theorem 2.22 (2b), p. 35 (case k = 1)

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

/-- Wendl, Theorem 2.22 (2b) (p. 35), case `k = 1`: let `p > 2` and let `J_ν → J` in `C^∞_loc`
be smooth almost complex structures on an open set `O ⊆ E`. If smooth `J_ν`-holomorphic maps
`u_ν` on the open unit disc, with values in a fixed compact `K₀ ⊆ O`, converge in `W^{1,p}` to a
smooth map `u`, then `u_ν → u` in `C^∞_loc` on the disc. -/
theorem tendstoCInftyLocOn_of_sobolevNorm_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ ∞ (u ν) (ball 0 1))
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) (ball 0 1) (u ν))
    (hmaps : ∀ ν, Set.MapsTo (u ν) (ball 0 1) K₀) (v : ℂ → E)
    (hv : ContDiffOn ℝ ∞ v (ball 0 1))
    (hlim : Tendsto (fun ν => sobolevNorm 1 (ENNReal.ofReal p) (ball 0 1) (u ν - v)) atTop
      (𝓝 0)) :
    TendstoCInftyLocOn u v (ball 0 1) := by
  sorry

end JHolomorphic
