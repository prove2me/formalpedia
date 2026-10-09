-- Prove2me | Theorems.Thm_KangKurtz_SCC_timescale_pieces_eq_3_27
-- name    : KangKurtz.SCC.timescale_pieces_eq_3_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:42.666843+00:00
-- url     : https://prove2.me/theorems/4a0feebc-8b2b-4bd1-ae09-8f427ed68c7e
-- title:
--   Equation (3.27), p. 17 — time-scale pieces bound the positive side
-- statement:
--   Let $\theta=\sum_j\theta^j$ be the component decomposition in Lemma 3.4. If the time-scale inequality (3.8) holds for every piece and $\Gamma^+_\theta$ is nonempty, then some species $i$ in the support of $\theta$ satisfies
--
--   $$\gamma+\max_{k\in\Gamma^+_\theta}\rho_k\le\alpha_i.$$
--
--   This is the positive-side bound (3.27) in the paper's uniform time-scale case. Along with the analogous negative-side bound, it yields (3.8) for the sum.
--
--   **Formalization Note** The finite maximum is expressed as a bound for every positive-side reaction using an attained species witness.
-- source:
--   Kang and Kurtz, Separation of time-scales and model reduction for stochastic reaction networks, arXiv:1011.1672v1, p. 17, §3.4, proof of Lemma 3.4, (3.8) implies (3.27)

import Mathlib
import Definitions.Def_KangKurtz_SCC_Setting

namespace KangKurtz.SCC

theorem timescale_pieces_eq_3_27
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
    (htime : ∀ j, TimeScale ν ν' α β γ (θs j))
    (hplus : (GammaPlus ν ν' θ).Nonempty) :
    ∃ i, θ i ≠ 0 ∧ ∀ k, k ∈ GammaPlus ν ν' θ → γ + rho ν α β k ≤ α i := by sorry
end KangKurtz.SCC
