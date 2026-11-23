-- Prove2me | Theorems.Thm_NoHair_asymptoticallyFlatEnd_timelike_access_at_infinity
-- name    : NoHair.asymptoticallyFlatEnd_timelike_access_at_infinity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:00:31.573369+00:00
-- url     : https://prove2.me/theorems/14a70bf7-b1e8-4d89-a611-39ac2fa304a5
-- title:
--   Every point of a sufficiently distant asymptotic end can send and receive timelike signals at all distances
-- statement:
--   Let $E$ be a time-oriented Lorentzian asymptotically flat end with chart $\psi$ and component decay constant $C$. Write $A_R=\psi(\{\rho>R\})$. If $R_0\ge R_E$ and $R_0\ge16|C|$, every $p\in A_{R_0}$ can send a future-directed timelike signal to $A_R$, and can receive one from $A_R$, for every $R\ge R_0$. Both signals are realized by globally $C^1$ curves in the mission's chronological relation. The argument is independent of the field equations and permits either time orientation.
-- source:
--   P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, pp. 6–7, equations (2.4)–(2.10) and the discussion of overlapping ends, https://arxiv.org/abs/0806.0016 . The numerical bound below is a sufficient estimate for the metric-component decay in the Prove2Me end chart.

import Definitions.Def_NoHair_chronologyAtInfinity

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem NoHair.asymptoticallyFlatEnd_timelike_access_at_infinity {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ)
    (hg : IsLorentzian g) (T : VecField M) (hT : IsTimeOrientation g T)
    (R₀ : ℝ) (hR : E.R ≤ R₀) (hC : 16 * |E.C| ≤ R₀) :
    let A := fun R : ℝ => E.ψ '' exteriorRegion R
    A R₀ ⊆ domainOfOuterCommunicationsAtInfinity g T A R₀ := by
  sorry
