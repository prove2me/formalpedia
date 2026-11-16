-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_Supplement_theorem_5_1
-- name    : InducedExpanderTest989.Structural.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:31:48.694754+00:00
-- url     : https://prove2.me/theorems/3dd4fb12-4327-4efb-ad87-fbac3f38d94e
-- title:
--   Theorem 5.1 — same-size distance testing for a large induced expander
-- statement:
--   Let $d\ge3$, $\alpha,\phi\in(0,1]$, $\varepsilon\in(0,1)$, $\delta\in(0,1/3]$, put $\kappa=1-\min\{1/4,\varepsilon/(8\alpha)\}$ and let $n\ge4/((1-\kappa)\alpha)$. Run Algorithm 1 (the mission's structural tester) with this $\kappa$, and let $\psi$ be its rejection threshold (21) at this $\kappa$. Define
--   $$\mu_n^{\rm stru}=\frac{\psi}{\phi^2},\qquad \mu_n^{\rm dist}=\frac{\mu_n^{\rm stru}}{2d+2}.$$
--   For every simple graph $G$ on $[n]$ of maximum degree at most $d$ and every adjacency-list ordering of $G$:
--   1. if $G\in\mathcal P_{\alpha,\phi}$, the tester accepts with probability at least $1-\delta$;
--   2. if $G$ is $\varepsilon$-far from $\mathcal P_{\alpha,\mu_n^{\rm dist}\phi^2}$, it rejects with probability at least $1-\delta$;
--   3. for every $d\ge3$ there is $C_d>0$ such that it makes at most
--   $$\min\Big\{dn,\ C_d\,\frac{\sqrt n\log n}{\phi^2}\cdot\frac{1-\kappa\alpha}{(1-\kappa)^2\alpha^{5/2}}\sqrt{\log\tfrac2\alpha\,\log\tfrac1{(1-\kappa)\alpha}}\cdot\log\tfrac1\delta\Big\}$$
--   adjacency-list queries;
--   4. for fixed $d,\alpha,\phi,\varepsilon,\delta$ and all sufficiently large $n$, its running time is at most a constant times the second term;
--   5. there are universal constants $c_1,c_2>0$ with
--   $$\frac{c_1}{2d+2}\,\vartheta_n\le\mu_n^{\rm dist}\le\frac{c_2}{2d+2}\,\vartheta_n,\qquad \vartheta_n=\frac{(1-\kappa)^2\alpha^3}{(1-\kappa\alpha)\log n\,\log\frac1{(1-\kappa)\alpha}\,\log\frac2\alpha}.$$
--
--   The structural tester therefore also solves distance testing at the original core size $\alpha n$, with the same query complexity and a rejection multiplier $\mu_n^{\rm dist}=\Theta_{\alpha,\varepsilon,d}(1/\log n)$. This is a companion theorem of the mission; it is not used in the proof of the goal.
--
--   **Formalization Note** The tester is the published `anchorTest n d α κ ϕ δ` at `κ = distKappa α ε`, and $\psi$ is `psi n α κ ϕ`; since $\kappa\ge3/4$ this is the multiplier of Theorem 4.1 at this $\kappa$. Rejection with probability at least $1-\delta$ is $1-\delta\le 1-\Pr[\text{accept}]$ (the tester always halts with a Boolean output). $\varepsilon$-far is the predicate `FarFrom` (strict, normalized by $dn$, targets of maximum degree at most $d$). The constant of clause 3 depends only on $d$; the constant and threshold of clause 4 depend on $(d,\alpha,\phi,\varepsilon,\delta)$; the constants of clause 5 are universal.
--
--   Differences from the source:
--   - encoding: Algorithm 1 run with κ = 1 − min{1/4, ε/(8α)} and ψ of (21) → the published anchorTest and psi at κ = distKappa α ε; reason: the same algorithm and threshold
--   - encoding: query complexity and running time "as in Theorem 4.1" → clauses 3–4: queries ≤ min{dn, C_d·(cost shape)} with C_d depending only on d, and running time ≤ C·(cost shape) for all n ≥ N₀ with C, N₀ depending on (d, α, ϕ, ε, δ); reason: Theorem 4.1's bounds at this κ, with the base mission's constant conventions
--   - reading: µ^stru is "the multiplier of Theorem 4.1 at the chosen κ" → clause 5 states its Θ-bounds (universal constants) divided by 2d + 2; reason: Theorem 4.1's multiplier carries the stated Θ, which the proof of Theorem 5.1 (PDF p. 36) substitutes and informal Theorem 1.3 states as Θ_{α,ε,d}(1/log n)
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.32 (PDF p.34), Theorem 5.1; multipliers p.34 (PDF p.36); informal Theorem 1.3 p.4 (PDF p.6)

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Algorithm
import Definitions.Def_InducedExpanderTest989_Structural_Supplement_Distance

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural.Supplement

/-- Peng–Shen, STOC 2027 #989, Theorem 5.1 (p. 32, PDF 34; multiplier on p. 34, PDF 36).
The tester is Algorithm 1 (`anchorTest`) run with `κ = distKappa α ε = 1 − min{1/4, ε/(8α)}`;
`ψ = psi n α κ ϕ` is (21), `µ^stru ϕ² = ψ` and `µ^dist ϕ² = ψ/(2d + 2)`. Clauses:
(1)–(2) completeness and soundness, (3) queries, (4) large-`n` running time,
(5) `µ^dist = µ^stru/(2d+2)` with `µ^stru = Θ(thetaShape)` and universal constants. -/
theorem theorem_5_1 :
    (∀ (n d : ℕ) (α ϕ ε δ : ℝ), 3 ≤ d → 0 < α → α ≤ 1 → 0 < ϕ → ϕ ≤ 1 → 0 < ε → ε < 1 →
      0 < δ → δ ≤ 1/3 → LargeEnough n α (distKappa α ε) →
      ∀ G : SimpleGraph (Fin n), DegreeBound d G → ∀ O : Oracle n d, IsAdjacencyList G O →
        (HasCore d G α ϕ → 1 - δ ≤ acceptProb O (anchorTest n d α (distKappa α ε) ϕ δ)) ∧
        (FarFrom d ε G (fun H => HasCore d H α (psi n α (distKappa α ε) ϕ / (2 * d + 2))) →
          1 - δ ≤ 1 - acceptProb O (anchorTest n d α (distKappa α ε) ϕ δ))) ∧
    (∀ d : ℕ, 3 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (α ϕ ε δ : ℝ), 0 < α → α ≤ 1 → 0 < ϕ → ϕ ≤ 1 → 0 < ε → ε < 1 →
        0 < δ → δ ≤ 1/3 → LargeEnough n α (distKappa α ε) →
        ∀ G : SimpleGraph (Fin n), DegreeBound d G → ∀ O : Oracle n d, IsAdjacencyList G O →
          Prog.queriesOn O (anchorTest n d α (distKappa α ε) ϕ δ) ≤ d * n ∧
          (Prog.queriesOn O (anchorTest n d α (distKappa α ε) ϕ δ) : ℝ) ≤
            C * costShape n α (distKappa α ε) ϕ δ) ∧
    (∀ (d : ℕ) (α ϕ ε δ : ℝ), 3 ≤ d → 0 < α → α ≤ 1 → 0 < ϕ → ϕ ≤ 1 → 0 < ε → ε < 1 →
      0 < δ → δ ≤ 1/3 →
      ∃ (C : ℝ) (N₀ : ℕ), 0 < C ∧ ∀ n : ℕ, N₀ ≤ n → LargeEnough n α (distKappa α ε) →
        ∀ G : SimpleGraph (Fin n), DegreeBound d G → ∀ O : Oracle n d, IsAdjacencyList G O →
          (Prog.timeOn O (anchorTest n d α (distKappa α ε) ϕ δ) : ℝ) ≤
            C * costShape n α (distKappa α ε) ϕ δ) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (n d : ℕ) (α ϕ ε : ℝ), 3 ≤ d → 0 < α → α ≤ 1 → 0 < ϕ → ϕ ≤ 1 → 0 < ε → ε < 1 →
        LargeEnough n α (distKappa α ε) →
        c₁ * thetaShape n α (distKappa α ε) / (2 * d + 2) ≤
            psi n α (distKappa α ε) ϕ / ϕ ^ 2 / (2 * d + 2) ∧
          psi n α (distKappa α ε) ϕ / ϕ ^ 2 / (2 * d + 2) ≤
            c₂ * thetaShape n α (distKappa α ε) / (2 * d + 2)) := by sorry

end InducedExpanderTest989.Structural.Supplement
