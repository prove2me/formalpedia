-- Prove2me | Theorems.Thm_KangKurtz_SCC_balance_pieces_eq_3_28
-- name    : KangKurtz.SCC.balance_pieces_eq_3_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:50:58.107002+00:00
-- url     : https://prove2.me/theorems/e43a153a-d275-4e9c-b3ee-970eca951986
-- title:
--   Equation (3.28), p. 17 — balanced pieces bound the positive side
-- statement:
--   Let $\theta=\sum_j\theta^j$ be the component decomposition in Lemma 3.4. If the balance equation (3.7) holds for every piece and $\Gamma^+_\theta$ is nonempty, then
--
--   $$\max_{k\in\Gamma^+_\theta}\rho_k\le\max_{k\in\Gamma^-_\theta}\rho_k.$$
--
--   This is the positive-side inequality (3.28) in the paper's uniform-balance case. Its negative-side counterpart is obtained by exchanging the two sign sets and contributes to the balance equality for $\theta$.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 17, §3.4, proof of Lemma 3.4, (3.7) implies (3.28)

import Mathlib
import Definitions.Def_KangKurtz_SCC_Setting

namespace KangKurtz.SCC

theorem balance_pieces_eq_3_28
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
    (hbal : ∀ j, Balance ν ν' α β (θs j))
    (hplus : (GammaPlus ν ν' θ).Nonempty) :
    maxRho ν α β (GammaPlus ν ν' θ) ≤ maxRho ν α β (GammaMinus ν ν' θ) := by sorry
end KangKurtz.SCC
