-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_anchorTest_structural_testing
-- name    : InducedExpanderTest989.Structural.anchorTest_structural_testing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:42.977583+00:00
-- url     : https://prove2.me/theorems/428f38a1-c3e2-4c1a-b62f-0898f68ee461
-- title:
--   Theorem 4.1 — structural testing over the full relaxation range
-- statement:
--   Let d≥1, 0<α,ϕ≤1, 0<δ≤1/3 and 0<κ<1. Write κ′=max{κ,3/4}, β=(1−κ′)α and assume n≥4/β. All parameters of Algorithm 1 are evaluated at κ′, including ψ=αβ/(64·1089ΛℓL) and L=⌊log₂(1/(α−β))⌋+1. Define
--   $$g=\frac{(1-\kappa')^2\alpha^3}{(1-\kappa'\alpha)\log n\log(1/((1-\kappa')\alpha))\log(2/\alpha)},$$
--   $$f=\frac{\sqrt n\log n}{\phi^2}\frac{1-\kappa'\alpha}{(1-\kappa')^2\alpha^{5/2}}\sqrt{\log(2/\alpha)\log(1/((1-\kappa')\alpha))}\log(1/\delta).$$
--   There are universal positive c₁,c₂, chosen before all parameters, with c₁g≤ψ/ϕ²≤c₂g for every admissible n,α,κ,ϕ. For every such tuple, every n-vertex graph G of maximum degree at most d and every valid adjacency list O, the concrete AnchorTest program satisfies
--   $$G\in P_{\alpha,\phi}\Rightarrow\Pr[\mathrm{accept}]\ge1-\delta,\qquad
--   G\notin P_{\kappa\alpha,\psi}\Rightarrow\Pr[\mathrm{reject}]\ge1-\delta.$$
--   The NO class uses the original κ. For each d there is a positive C_d, uniform in all remaining parameters and G,O, for which worst-case queries are at most dn and C_df. For each fixed admissible d,α,κ,ϕ,δ there are C>0 and an integer N₀ such that for every n≥N₀ satisfying the size condition and every G,O, worst-case time is at most Cf. Counts maximize over internal randomness and are computed from the program. These are all clauses of the full structural testing guarantee.
--
--   Differences from the source:
--   - generalization: Theorem 4.1 uses 3/4≤κ<1 → 0<κ<1 with Algorithm 1 evaluated at κ′=max{κ,3/4}, retaining original κ in the NO class; reason: the following paragraph on the same page proves this reduction; for κ≥3/4 it is Algorithm 1 itself
--   - encoding: vertices [n], slots [d], null symbol ⊥ → Fin n, zero-based Fin d slots, none; reason: renumbering preserves every adjacency list and graph
--   - encoding: Algorithm 1 with unit-cost sampling, walk, sort and search operations → finite oracle program trees with computed probabilities and worst-case query and tick counts; reason: each random draw and query is a constructor; table writes, moves, storage, merge-sort comparisons, binary-search probes, counters, tests and parameter arithmetic are charged
--   - encoding: real parameters, natural logarithms and integer ceilings → Real.log, Real.sqrt, Nat.ceil and real powers; reason: all arguments have their stated positive domains; Nat.ceil agrees with the paper on those domains
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.15 (PDF p.17), Theorem 4.1 and its following κ-reduction paragraph; Algorithm 1 p.16; (21) p.30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

theorem anchorTest_structural_testing  :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (n : ℕ) (α κ ϕ : ℝ), 0 < κ → κ < 1 →
        BaseParams α (effectiveKappa κ) ϕ → LargeEnough n α (effectiveKappa κ) →
        c₁ * thetaShape n α (effectiveKappa κ) ≤ psi n α (effectiveKappa κ) ϕ / ϕ^2 ∧
        psi n α (effectiveKappa κ) ϕ / ϕ^2 ≤ c₂ * thetaShape n α (effectiveKappa κ)) ∧
    (∀ (n d : ℕ) (α κ ϕ δ : ℝ), Admissible n d α κ ϕ δ →
      ∀ G : SimpleGraph (Fin n), DegreeBound d G → ∀ O : Oracle n d, IsAdjacencyList G O →
        (HasCore d G α ϕ → 1-δ ≤ acceptProb O (anchorTest n d α κ ϕ δ)) ∧
        (¬ HasCore d G (κ*α) (psi n α (effectiveKappa κ) ϕ) →
          1-δ ≤ 1-acceptProb O (anchorTest n d α κ ϕ δ))) ∧
    (∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (α κ ϕ δ : ℝ), Admissible n d α κ ϕ δ →
      ∀ G : SimpleGraph (Fin n), DegreeBound d G → ∀ O : Oracle n d, IsAdjacencyList G O →
        Prog.queriesOn O (anchorTest n d α κ ϕ δ) ≤ d*n ∧
        (Prog.queriesOn O (anchorTest n d α κ ϕ δ) : ℝ) ≤
          C * costShape n α (effectiveKappa κ) ϕ δ) ∧
    (∀ (d : ℕ) (α κ ϕ δ : ℝ), 1 ≤ d →
      (0 < α ∧ α ≤ 1 ∧ 0 < κ ∧ κ < 1 ∧ 0 < ϕ ∧ ϕ ≤ 1 ∧ 0 < δ ∧ δ ≤ 1/3) →
      ∃ (C : ℝ) (N₀ : ℕ), 0 < C ∧ ∀ n : ℕ, N₀ ≤ n →
        LargeEnough n α (effectiveKappa κ) → ∀ G : SimpleGraph (Fin n), DegreeBound d G →
        ∀ O : Oracle n d, IsAdjacencyList G O →
          (Prog.timeOn O (anchorTest n d α κ ϕ δ) : ℝ) ≤
            C * costShape n α (effectiveKappa κ) ϕ δ) := by sorry

end InducedExpanderTest989.Structural
