-- Prove2me | Theorems.Thm_LuoSunLiu_PLBLower_proposition_2
-- name    : LuoSunLiu.PLBLower.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:59.435174+00:00
-- url     : https://prove2.me/theorems/dad995c0-adc1-481d-ba71-446f7a41fe19
-- title:
--   Proposition 2, p. 22 — every algorithm has E(R^{PLB}_{T₀}) ≥ C₀C_pT₀ on some PLB with ξ_t ∈ PB(ξ̃, C_p), C₀ depending only on ξ̃
-- statement:
--   Let $d\ge2$ and let $\tilde\xi\in\mathbb R^d$ have all entries positive. Then there is a constant $C_0>0$, depending only on $\tilde\xi$, with the following property.
--
--   Let $C_p\ge0$ satisfy $C_p/2<\min_{i\in[d]}\tilde\xi_i$, let $(\Omega,P)$ be a probability space carrying a measurable noise process $(\eta_t)_{t\ge1}$, and let $\mathcal A^*$ be any (possibly randomized) algorithm. Then there exist deterministic parameters $(\xi_t)_{t\ge1}$ and nonempty finite action sets $(\mathcal A_t)_{t\ge1}$ such that
--
--   1. $\xi_t\in PB(\tilde\xi,C_p)$, i.e. $\|\xi_t-\tilde\xi\|_\infty\le C_p/2$, for every $t$;
--   2. $\|\xi_s-\xi_t\|_\infty\le C_p$ for all $s,t$, so the rewards $Z_t=\langle\xi_t,A_t\rangle+\eta_t$ form a perturbed linear bandit with perturbation $C_p$;
--   3. every action $a\in\mathcal A_t$ has exactly one nonzero entry and $|\langle\xi_t,a\rangle|\le1$ (Conditions 1 and 3 of the paper's upper bound);
--   4. when $\mathcal A^*$ is run on this bandit, for every horizon $T_0\ge1$
--   $$\mathbb E\big(R^{PLB}_{T_0}(\mathcal A^*)\big)\ \ge\ C_0\,C_p\,T_0 .$$
--
--   The regret of every algorithm therefore grows linearly in $C_pT_0$ in the worst case, so the linear term $2a_{\max}C_pT_0$ in the paper's upper bound for M-LinUCB (Lemma 3) cannot be removed: adversarial perturbations of size $C_p$ force regret of order $C_pT_0$.
--
--   **Formalization Note** The hypothesis $d\ge2$ is added: the paper's proof uses the second smallest entry of $\tilde\xi$, and for $d=1$ the statement is false (all parameters in $PB(\tilde\xi,C_p)$ are positive, so always playing the largest action has zero regret). The hypothesis $C_p\ge0$ makes $PB(\tilde\xi,C_p)$ nonempty. The constant $C_0$ is quantified after $\tilde\xi$ and before $C_p$, the probability space, the noise, the algorithm and $T_0$. The parameters and action sets are deterministic and are chosen after the algorithm and the noise are fixed, as in the paper's construction. The noise is an arbitrary measurable process: the paper's PLB asks for conditionally sub-Gaussian noise, and since $\eta\equiv0$ is admissible, quantifying over all noise processes is stronger than the printed existence statement. The algorithm may use its own randomness and the noise through $\omega$ and sees past actions, past rewards and the current action set. The expectation is the lower Lebesgue integral of the nonnegative regret. Arms are `Fin d`, 0-based; periods are 1-based. Conclusions 2 and 3 are not in the printed statement and only strengthen it.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, p. 22, Proposition 2 (restated p. 44 with 'a PLB (Z_t = ⟨ξ_t, A_t⟩ + η_t)'); proof pp. 44–46

import Mathlib
import Definitions.Def_LuoSunLiu_PLBLower_Model

open MeasureTheory

namespace LuoSunLiu.PLBLower

/-- Proposition 2 (p. 22; restated p. 44). For every central parameter `ξ̃` with positive entries
(and `d ≥ 2`) there is `C_0 > 0`, depending only on `ξ̃`, such that for every `C_p ≥ 0` with
`C_p / 2 < min_i ξ̃_i`, every probability space, every measurable noise process `η` and every
algorithm, there are deterministic parameters `ξ_t ∈ PB(ξ̃, C_p)` and nonempty finite action sets
`𝒜_t` (single-nonzero-entry actions with `|⟨ξ_t, a⟩| ≤ 1`) forming a PLB with perturbation `C_p`,
on which `E(R^{PLB}_{T_0}) ≥ C_0 C_p T_0` for every `T_0 ≥ 1`. -/
theorem proposition_2 (d : ℕ) (hd : 2 ≤ d) (ξc : Fin d → ℝ) (hξc : ∀ i, 0 < ξc i) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ Cp : ℝ, 0 ≤ Cp → (∀ i, Cp / 2 < ξc i) →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : ℕ → Ω → ℝ), (∀ t, Measurable (η t)) →
      ∀ alg : Algorithm d Ω,
      ∃ (ξ : ℕ → Fin d → ℝ) (𝒜 : ℕ → Finset (Fin d → ℝ)),
        (∀ t, ξ t ∈ PB ξc Cp) ∧ IsPerturbed ξ Cp ∧
        (∀ t, (𝒜 t).Nonempty) ∧
        (∀ t, ∀ a ∈ 𝒜 t,
          (∃ j : Fin d, ∃ c : ℝ, c ≠ 0 ∧ a = Pi.single j c) ∧ |ξ t ⬝ᵥ a| ≤ 1) ∧
        ∀ T0 : ℕ, 1 ≤ T0 →
          ENNReal.ofReal (C0 * Cp * T0) ≤
            ∫⁻ ω, ENNReal.ofReal (regret alg ξ 𝒜 η T0 ω) ∂P := by sorry

end LuoSunLiu.PLBLower
