-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_theorem_6
-- name    : NeedPersuasion.FirstBest.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:49.245981+00:00
-- url     : https://prove2.me/theorems/ec4eaadf-a0ed-4c52-88a0-92ff550756ab
-- title:
--   Theorem 6, p. 20 — sm(θ) = ap(θ) for all θ if λ_H ≥ Λ̄_H; otherwise for θ > θ(λ_L, λ_H), with sm(θ) constant below
-- statement:
--   For a weight $\theta\in[0,1]$ let $\mathrm{sm}(\theta)$ be the set of signaling mechanisms maximizing $W(\pi,\theta)=\theta W_L(\pi)+(1-\theta)W_H(\pi)$ over $\Pi_{SM}$, and $\mathrm{ap}(\theta)$ the set of admission policies maximizing it over $\Pi_{AP}$ (the first-best). Let $\bar\Lambda_H\in(0,1)$ be the root of $g(x)=\sum_k(1-x)x^ku_L(k)$. Then:
--
--   1. if $\lambda_H\ge\bar\Lambda_H$, then $\mathrm{sm}(\theta)=\mathrm{ap}(\theta)$ for all $\theta\in[0,1]$;
--   2. if $\lambda_H<\bar\Lambda_H$, there is $\bar\theta=\theta(\lambda_L,\lambda_H)\in(0,1]$ such that
--   $$\mathrm{sm}(\theta)=\mathrm{ap}(\theta)\ \text{ for all }\theta\in(\bar\theta,1],\qquad \mathrm{sm}(\theta)=\mathrm{sm}(\theta')\ \text{ for all }\theta,\theta'\in[0,\bar\theta).$$
--
--   So for a wide range of weights the obedience constraints cost nothing: the optimal signaling mechanism is the first-best admission policy.
--
--   **Formalization Note** $\mathrm{sm}(\theta)$ and $\mathrm{ap}(\theta)$ are sets of maximizers (footnote 14); at $\theta=0$ ($\theta=1$) they are refined lexicographically, maximizing $W_H$ then $W_L$ ($W_L$ then $W_H$), as in footnote 12. "$\lambda_H\in[\bar\Lambda_H,1]$" is $\lambda_H\ge\bar\Lambda_H$ under the standing $\lambda\le1$. "Independent of $\theta$" is equality of the sets. $\bar\theta=1$ is allowed, as on p. 44. Lemma 2's hypothesis ($\lambda<1$, or $u_L,u_H\to-\infty$) and convergence of $\sum_k\lambda_H^ku_H(k)$ are added so that the compared optimizer sets are non-empty under the finite-welfare convention for $\Pi_{AP}$. $\bar\Lambda_H$ enters as any $\Lambda\in(0,1)$ with $g(\Lambda)=0$, which is unique.
-- source:
--   arXiv:2005.07253v3, Theorem 6, p. 20; footnotes 12 (p. 13) and 14 (p. 20)

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

namespace NeedPersuasion.FirstBest

theorem theorem_6 (M : Model) (hM : M.Standing)
    (hExist : M.lam < 1 ∨ (Filter.Tendsto M.uL Filter.atTop Filter.atBot ∧
      Filter.Tendsto M.uH Filter.atTop Filter.atBot))
    (hSumH : Summable (fun k => M.lamH ^ k * M.uH k))
    (Λ : ℝ) (hΛ : Λ ∈ Set.Ioo (0 : ℝ) 1 ∧ g M Λ = 0) :
    (Λ ≤ M.lamH → ∀ θ ∈ Set.Icc (0 : ℝ) 1, smSet M θ = apSet M θ) ∧
    (M.lamH < Λ → ∃ θbar ∈ Set.Ioc (0 : ℝ) 1,
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, θbar < θ → smSet M θ = apSet M θ) ∧
      ∀ θ ∈ Set.Ico (0 : ℝ) θbar, ∀ θ' ∈ Set.Ico (0 : ℝ) θbar, smSet M θ = smSet M θ') := by sorry

end NeedPersuasion.FirstBest
