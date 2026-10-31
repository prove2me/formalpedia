-- Prove2me | Theorems.Thm_LimitedPersuasion_rhoE_eq_of_symmetric
-- name    : LimitedPersuasion.rhoE_eq_of_symmetric
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:55.519877+00:00
-- url     : https://prove2.me/theorems/063dd4e0-2c4e-43f3-9129-e6c683b3c801
-- title:
--   In a symmetric instance $\varrho_E=\sum_{\boldsymbol\theta}q_{\boldsymbol\theta}\,\varrho(\theta_i)$ for every action $i$
-- statement:
--   Let $q$ be a symmetric prior over states $\boldsymbol\theta=(\theta_1,\dots,\theta_n)$, i.e. $q_{\boldsymbol\theta}=q_{\boldsymbol\theta'}$ whenever $\boldsymbol\theta'$ is a permutation of $\boldsymbol\theta$. Then every fixed action gives the receiver the same expected utility, so the best of them, $\varrho_E=\max_{i\in[n]}\sum_{\boldsymbol\theta}q_{\boldsymbol\theta}\varrho(\theta_i)$, satisfies
--   $$\varrho_E=\sum_{\boldsymbol\theta}q_{\boldsymbol\theta}\,\varrho(\theta_i)\qquad\text{for every }i\in[n].$$
--
--   This identity is used in the proof of Lemma 3: the never-recommended actions of a symmetric scheme have expected value exactly $\varrho_E$.
--
--   Differences from the source:
--   - encoding: type sets $\Theta_i$ and a distribution over $\Theta$ → one finite type set $T$, states $\mathrm{Fin}\,n\to T$, prior a weight function; reason: Lean convention, same instances
-- source:
--   Gradwohl–Hahn–Hoefer–Smorodinsky, Algorithms for Persuasion with Limited Communication, arXiv:2007.12489v2, §2 "Symmetric Instances", display "In particular, due to symmetry, ϱ_E = Σ_θ q_θ · ϱ(θ_i) for every i ∈ [n]", p.5

import Mathlib
import Definitions.Def_LimitedPersuasion_Model

namespace LimitedPersuasion

/-- **`ϱ_E` in a symmetric instance**, Gradwohl–Hahn–Hoefer–Smorodinsky, arXiv:2007.12489v2,
§2 "Symmetric Instances", display "In particular, due to symmetry, …", p.5: in a symmetric
instance every fixed action gives the receiver the same expected utility, so
`ϱ_E = ∑_θ q_θ · ϱ(θᵢ)` for every `i ∈ [n]`. -/
theorem rhoE_eq_of_symmetric {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ} [NeZero n]
    (I : Instance T n) (hsym : I.IsSymmetric) (i : Fin n) :
    I.rhoE = ∑ θ, I.q θ * I.ρ (θ i) := by sorry

end LimitedPersuasion
