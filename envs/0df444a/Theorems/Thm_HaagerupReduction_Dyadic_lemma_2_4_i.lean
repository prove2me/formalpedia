-- Prove2me | Theorems.Thm_HaagerupReduction_Dyadic_lemma_2_4_i
-- name    : HaagerupReduction.Dyadic.lemma_2_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:05.366362+00:00
-- url     : https://prove2.me/theorems/a2e11e72-a344-4e88-bc13-ad38b9fa778f
-- title:
--   Lemma 2.4 (i), p. 7 — the modular group σ^{ϕ_n} of ϕ_n(x) = φ̂(e^{-a_n}x) is 2^{-n}-periodic, n ≥ 1
-- statement:
--   Let $\mathcal R = M\rtimes_{\sigma^\varphi}G$, $\hat\xi$, $\hat\varphi$ and $a_n = 2^nb_n$ be as in the model, let $n\ge 1$, and let
--   $$\varphi_n(x) = \hat\varphi(e^{-a_n}x), \qquad x\in\mathcal R$$
--   (display (2.3)). For $x\in\mathcal R$, $\varphi_n(x) = \langle x\eta_n,\eta_n\rangle$ with $\eta_n = e^{-a_n/2}\hat\xi$. Let $S_n$ be modular data of $(\mathcal R, \varphi_n)$: $S_n.M = \mathcal R$ and $S_n.\xi = \eta_n/\|\eta_n\|$, with modular group $\sigma^{\varphi_n}_t$. Then $\sigma^{\varphi_n}$ is $2^{-n}$-periodic:
--   $$\sigma^{\varphi_n}_{t+2^{-n}}(x) = \sigma^{\varphi_n}_t(x), \qquad t\in\mathbb R,\ x\in\mathcal R.$$
--
--   Periodicity is what makes the centralizer $\mathcal R_{\varphi_n}$ large enough to be the range of the averaging expectation in Lemma 2.4 (ii).
--
--   **Formalization Note.** The modular data of $\varphi_n$ are a hypothesis $S_n$; the cyclic separating vector is $\eta_n$ normalized, since $\varphi_n$ need not be a state and a positive multiple of a functional has the same modular group.
-- source:
--   Haagerup, Junge & Xu, A reduction method for noncommutative Lp-spaces and applications, arXiv:0806.3635v2, p. 7, Lemma 2.4 (i), with (2.3) p. 7

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HaagerupReduction_Dyadic_Model

namespace HaagerupReduction.Dyadic

universe u

open OAI.BoundedRecovery
open Filter Topology

/-- Lemma 2.4 (i): the modular group of `ϕ_n` is `2^{-n}`-periodic (`n ≥ 1`). -/
theorem lemma_2_4_i {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H) (n : ℕ) (hn : 1 ≤ n)
    (Sn : StandardModularData (L2G H)) (hM : Sn.M = crossedProduct S)
    (hxi : Sn.xi = ((‖etaN S n‖⁻¹ : ℝ) : ℂ) • etaN S n) :
    ∀ t : ℝ, ∀ x ∈ crossedProduct S, Sn.sigma (t + (2 : ℝ)⁻¹ ^ n) x = Sn.sigma t x := by sorry

end HaagerupReduction.Dyadic
