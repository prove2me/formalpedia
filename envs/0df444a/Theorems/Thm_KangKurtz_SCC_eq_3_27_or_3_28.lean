-- Prove2me | Theorems.Thm_KangKurtz_SCC_eq_3_27_or_3_28
-- name    : KangKurtz.SCC.eq_3_27_or_3_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:51:00.595699+00:00
-- url     : https://prove2.me/theorems/62364a75-cb04-471f-9a2e-17467db99b6e
-- title:
--   Equations (3.27) or (3.28), p. 16 — the positive-side dichotomy
-- statement:
--   Let $\theta=\sum_j\theta^j$ be the component decomposition in Lemma 3.4, and suppose Condition 3.2 holds for every piece. If $\Gamma^+_\theta$ is nonempty, then either its largest effective exponent satisfies the time-scale bound at some species in the support of $\theta$, or it does not exceed the largest effective exponent on $\Gamma^-_\theta$:
--
--   $$
--   \left(\exists i\in\operatorname{supp}(\theta),\quad
--     \gamma+\max_{k\in\Gamma^+_\theta}\rho_k\le\alpha_i\right)
--   \quad\text{or}\quad
--   \max_{k\in\Gamma^+_\theta}\rho_k\le
--   \max_{k\in\Gamma^-_\theta}\rho_k.
--   $$
--
--   This is the positive-side dichotomy (3.27)/(3.28) used by the goal theorem.
--
--   **Formalization Note** The first alternative uses an attained species witness and a bound for every positive-side reaction; this avoids arithmetic on an extended maximum and is equivalent to (3.27) for the finite nonempty set.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, pp. 15–16, §3.4, proof of Lemma 3.4, (3.27)–(3.28)

import Mathlib
import Definitions.Def_KangKurtz_SCC_Setting

namespace KangKurtz.SCC

theorem eq_3_27_or_3_28
    {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ)
    (hbinary : BinaryReactions ν)
    (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ) (γ : ℝ)
    (θ : Fin s → ℝ) (hθ : ∀ i, 0 ≤ θ i)
    {m : ℕ} (θs : Fin m → Fin s → ℝ)
    (hθs : ∀ j i, 0 ≤ θs j i)
    (hsum : θ = ∑ j, θs j)
    (hone : ∀ j i i', θs j i ≠ 0 → θs j i' ≠ 0 → SameComp ν ν' i i')
    (hdist : ∀ j j', j ≠ j' → ∀ i i',
      θs j i ≠ 0 → θs j' i' ≠ 0 → ¬ SameComp ν ν' i i')
    (hcond : ∀ j, Cond32 ν ν' α β γ (θs j))
    (hplus : (GammaPlus ν ν' θ).Nonempty) :
    (∃ i, θ i ≠ 0 ∧ ∀ k, k ∈ GammaPlus ν ν' θ → γ + rho ν α β k ≤ α i) ∨
      maxRho ν α β (GammaPlus ν ν' θ) ≤ maxRho ν α β (GammaMinus ν ν' θ) := by sorry
end KangKurtz.SCC
