-- Prove2me | Theorems.Thm_MechanismDesign_VCG_efficient_dsic_is_vcg
-- name    : MechanismDesign.VCG.efficient_dsic_is_vcg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T03:17:49.048338+00:00
-- url     : https://prove2.me/theorems/a0af0949-20d2-48cb-9a70-e2b9ba1b35fc
-- title:
--   Corollary 7.1 -- every DSIC mechanism with an efficient decision rule is VCG (Green–Laffont, Holmström)
-- statement:
--   In the dominant-strategy model of Chapter 7, suppose that for every agent $i$ the type set $\Theta_i$ is a convex subset of a finite-dimensional Euclidean space $\mathbb R^{d_i}$, and that for every alternative $a$ the function $\theta_i \mapsto u_i(a, \theta_i)$ is convex and continuous on $\Theta_i$. Let $(q, t_1, \dots, t_N)$ be a dominant strategy incentive-compatible mechanism whose decision rule $q$ is efficient. Then $(q, t_1, \dots, t_N)$ is a VCG mechanism: for every agent $i$ there is a function $\tau_i : \Theta_{-i} \to \mathbb R$ with
--
--   $$
--   t_i(\theta) = -\sum_{j \ne i} u_j(q(\theta), \theta_j) + \tau_i(\theta_{-i}) \qquad \text{for all } \theta \in \Theta .
--   $$
--
--   This is the uniqueness theorem of Green and Laffont (1977) and Holmström (1979): on convex domains VCG mechanisms are not only sufficient but the only way to implement efficient decisions in dominant strategies. Combined with Proposition 7.10 it characterizes when efficient decisions can be implemented in dominant strategies with a balanced budget.
--
--   **Formalization Note** The book assumes only that $u_i(a,\cdot)$ is convex; continuity on $\Theta_i$ is added because the statement is false without it. Counterexample: one agent, $\Theta_1 = [0,1] \subset \mathbb R$, $A = \{a, b\}$, $u_1(a,\cdot) = 0$, $u_1(b,\theta) = 1$ if $\theta = 1$ and $0$ otherwise (convex on $[0,1]$), $q(\theta) = b$ iff $\theta = 1$ (efficient), $t_1(\theta) = \tfrac12$ if $\theta = 1$ and $0$ otherwise; this mechanism is DSIC, but a VCG transfer of a single agent is a constant. Dummy agents with a single type and zero utility extend the counterexample to any number of agents. The type set of agent $i$ is the subtype of a set `S i` in `EuclideanSpace ℝ (Fin (d i))`.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.134, Corollary 7.1 (continuity of u_i(a,·) added; see Formalization Note)

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace MechanismDesign.VCG

/-- Börgers, Corollary 7.1 (p.134), Green–Laffont (1977) and Holmström (1979), with continuity
added (see the natural-language statement): each type set `Θᵢ = Sᵢ` is a convex subset of the
Euclidean space `ℝ^{dᵢ}` and each `uᵢ(a, ·)` is convex and continuous on `Sᵢ`. Every dominant
strategy incentive-compatible mechanism `(q, t₁, …, t_N)` with an efficient decision rule `q`
is a VCG mechanism: `tᵢ(θ) = −∑_{j ≠ i} u_j(q(θ), θ_j) + τᵢ(θ₋ᵢ)` for some `τᵢ : Θ₋ᵢ → ℝ`. -/
theorem efficient_dsic_is_vcg {ι A : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (S : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))) (hS : ∀ i, Convex ℝ (S i))
    (u : ∀ i, A → EuclideanSpace ℝ (Fin (d i)) → ℝ)
    (hconv : ∀ i a, ConvexOn ℝ (S i) (u i a))
    (hcont : ∀ i a, ContinuousOn (u i a) (S i))
    (M : DirectMechanism (fun i => ↥(S i)) A)
    (hM : DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) M)
    (heff : IsEfficient (Θ := fun i => ↥(S i)) (fun i a x => u i a x) M.q) :
    IsVCG (Θ := fun i => ↥(S i)) (fun i a x => u i a x) M := by sorry

end MechanismDesign.VCG
