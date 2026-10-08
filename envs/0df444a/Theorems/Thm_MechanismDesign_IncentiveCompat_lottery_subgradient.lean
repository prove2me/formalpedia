-- Prove2me | Theorems.Thm_MechanismDesign_IncentiveCompat_lottery_subgradient
-- name    : MechanismDesign.IncentiveCompat.lottery_subgradient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:12:13.828992+00:00
-- url     : https://prove2.me/theorems/12998d2d-c632-4eaf-9479-a66b29cd19a0
-- title:
--   Proposition 5.3 -- with lottery outcomes, q is implementable iff q(θ) is a subgradient of a convex U
-- statement:
--   Let $\Omega$ be a finite set of outcomes and let the alternatives be all lotteries $p \in \Delta(\Omega) = \{p \in \mathbb R^\Omega : p_\ell \ge 0,\ \sum_\ell p_\ell = 1\}$. Let the type set $\Theta \subseteq \mathbb R^\Omega$ be a nonempty convex set of vectors of Bernoulli utilities, and let the utility of lottery $p$ for type $\theta$ be the expected utility $p\cdot\theta = \sum_{\ell} p_\ell\theta_\ell$. Then a decision rule $q : \Theta \to \Delta(\Omega)$ is implementable if and only if there is a function $U : \Theta \to \mathbb R$, convex on $\Theta$, such that for every $\theta \in \Theta$ the vector $q(\theta)$ is a subgradient of $U$ at $\theta$:
--   $$U(\theta') \;\ge\; U(\theta) + q(\theta)\cdot(\theta' - \theta)\qquad\text{for all } \theta' \in \Theta.$$
--
--   This is the lottery case of Rochet's theorem in the language of convex analysis.
--
--   **Formalization Note** The page writes "$U : \theta \to \mathbb R$"; the intended domain is the type set $\Theta$. In Lean `U` is a function on $\mathbb R^\Omega$ of which only the values on $\Theta$ matter (convexity and the subgradient inequality are both relative to $\Theta$). `Θ` is the subtype of a set `S`; nonemptiness is the standing assumption of §5.2.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.103, Proposition 5.3

import Mathlib
import Definitions.Def_MechanismDesign_IncentiveCompat_Model

namespace MechanismDesign.IncentiveCompat

/-- Proposition 5.3 (p.103). Alternatives are the lotteries `Δ(Ω)` over a finite outcome set
`Ω`; types are the vectors `θ ∈ S ⊆ ℝ^Ω` of Bernoulli utilities, `S` nonempty and convex; the
utility of lottery `p` for type `θ` is `p · θ`. Then `q` is implementable if and only if there
is a function `U`, convex on `S`, such that `q(θ)` is a subgradient of `U` at `θ` (relative
to `S`) for every `θ ∈ S`. -/
theorem lottery_subgradient {Ω : Type*} [Fintype Ω] (S : Set (Ω → ℝ)) (hS : Convex ℝ S)
    (hSne : S.Nonempty) (q : S → stdSimplex ℝ Ω) :
    Implementable (fun (p : stdSimplex ℝ Ω) (θ : S) => lotteryUtility p (θ : Ω → ℝ)) q ↔
      ∃ U : (Ω → ℝ) → ℝ, ConvexOn ℝ S U ∧
        ∀ θ : S, IsSubgradientOn S U (θ : Ω → ℝ) ((q θ : stdSimplex ℝ Ω) : Ω → ℝ) := by sorry

end MechanismDesign.IncentiveCompat
