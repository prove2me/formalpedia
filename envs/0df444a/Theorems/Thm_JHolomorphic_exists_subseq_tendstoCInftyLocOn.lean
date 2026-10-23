-- Prove2me | Theorems.Thm_JHolomorphic_exists_subseq_tendstoCInftyLocOn
-- name    : JHolomorphic.exists_subseq_tendstoCInftyLocOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T20:33:34.565326+00:00
-- url     : https://prove2.me/theorems/c9e6344b-674e-4850-80e0-dd8b85f37450
-- title:
--   $C^1$-bounded pseudoholomorphic discs have $C^\infty_{\mathrm{loc}}$-convergent subsequences
-- statement:
--   Let $E$ be a finite-dimensional real vector space, $O\subseteq E$ open, and let $J_\nu$, $J$ be smooth almost complex structures on $O$ with $J_\nu\to J$ in $C^\infty_{\mathrm{loc}}$ on $O$. Let $K_0\subseteq O$ be compact and let $D\subset\mathbb{C}$ be the open unit disc. Let $u_\nu:D\to K_0$ be $C^1$ maps with $\partial_su_\nu+J_\nu(u_\nu)\,\partial_tu_\nu=0$ on $D$ and
--   $$\sup_\nu\sup_{z\in D}\|Du_\nu(z)\|<\infty.$$
--   Then a subsequence $u_{\nu_k}$ converges in $C^\infty_{\mathrm{loc}}$ on $D$ to a $C^\infty$ map $v:D\to K_0$ with $\partial_sv+J(v)\,\partial_tv=0$.
--
--   **Formalization Note** The hypotheses on the structures are `IsAlmostComplexOn J O`, `∀ ν, IsAlmostComplexOn (Jν ν) O` and `TendstoCInftyLocOn Jν J O`. Because $J$ is only defined on $O$, the maps are required to take values in the fixed compact set $K_0\subseteq O$ (`Set.MapsTo (u ν) (ball 0 1) K₀`). The maps are `ContDiffOn ℝ 1` on the disc (Wendl leaves the regularity class implicit), and the derivative bound is `‖fderiv ℝ (u ν) z‖ ≤ C` for $z\in D$. The subsequence is `u ∘ φ` for a `StrictMono` map $\mathbb{N}\to\mathbb{N}$, and the limit satisfies `ContDiffOn ℝ ∞`, `IsJHolomorphicOn J (ball 0 1)` and `Set.MapsTo v (ball 0 1) K₀`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 9, Proposition 9.1, p. 151

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

/-- Wendl, Proposition 9.1 (p. 151): let `J_ν → J` in `C^∞_loc` be smooth almost complex
structures on an open set `O ⊆ E`. Every sequence of `C¹` maps `u_ν` on the open unit disc that are
`J_ν`-holomorphic, take values in a fixed compact `K₀ ⊆ O` and have uniformly bounded first
derivative has a subsequence converging in `C^∞_loc` on the disc; the limit is a `C^∞`
`J`-holomorphic map with values in `K₀`. -/
theorem exists_subseq_tendstoCInftyLocOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ 1 (u ν) (ball 0 1))
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) (ball 0 1) (u ν))
    (hmaps : ∀ ν, Set.MapsTo (u ν) (ball 0 1) K₀) (C : ℝ)
    (hC : ∀ ν, ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (u ν) z‖ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℂ → E, ContDiffOn ℝ ∞ v (ball 0 1) ∧
      IsJHolomorphicOn J (ball 0 1) v ∧ Set.MapsTo v (ball 0 1) K₀ ∧
      TendstoCInftyLocOn (fun ν => u (φ ν)) v (ball 0 1) := by
  sorry

end JHolomorphic
