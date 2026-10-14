-- Prove2me | Theorems.Thm_GMCPBandit_Regret_proposition_4
-- name    : GMCPBandit.Regret.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:38.487396+00:00
-- url     : https://prove2.me/theorems/f552913d-43a2-44f4-a0a6-eb026381f7d6
-- title:
--   Proposition 4, p. 18 — ℙ(‖β^random − β^true‖₁ ≤ min{1/(σ₂x_max), h/(4eσ₂R_max x_max)}) ≥ 1 − 15/(T+1)
-- statement:
--   Work in the model of §3 under Assumptions A.1, A.3, A.4 and A.5. Let $a>2304s/(p^*\kappa)$. There are constants $C_0\ge\max\{10,16/p^*\}$ and $C_5>0$ such that the following holds when the G-MCP-Bandit runs with $t_0=2C_0|\mathcal K|$ and $\lambda_{1,0}=C_5$. For every 2sWL selection rule, every $T\ge\max\{(t_0+1)^2/e^2-1,e\}$ and every optimal decision $k\in\mathcal K_o$, the random-sample MCP estimator $\beta^{MCP}=\beta^{random}_k(T)$, the 2sWL estimate on $\mathcal R_k(T)$ with $\lambda=\lambda_1(T)=C_5\sqrt{1+\log d/\log(T+1)}$, satisfies
--   $$\mathbb P\Big(\|\beta^{MCP}-\beta^{true}_k\|_1\le\min\Big\{\frac1{\sigma_2x_{\max}},\frac{h}{4e\sigma_2R_{\max}x_{\max}}\Big\}\Big)\ge1-\frac{15}{T+1}.$$
--
--   In the paper's proof (Lemma EC.9) $C_5=\beta_{\min}p^*\kappa/\big((2304s+ap^*\kappa)\sqrt{1+\log d}\big)$. The radius is exactly the one under which the random-sample estimates separate the optimal decision from the others by $h/2$ (Lemma EC.10), so this proposition controls the upper level of the bi-level decision.
--
--   **Formalization Note** The proposition names neither the algorithm's parameters nor a threshold on $T$; both are taken from Lemma EC.9, whose proof is the proposition's proof. $C_0$ and $C_5$ are existential, placed after the model and $a$ and before the probability space, the selection rule and $T$. The estimator is stated for $k\in\mathcal K_o$, where A.4 and $U_k$ give identifiability. Lemma EC.9 states its bound for the oracle estimator; the proposition and the proof concern the 2sWL estimate, which is what is formalized. The estimate uses only exploration data, so no trajectory is needed.
-- source:
--   Wang, Wei and Yao, Online Learning and Decision-Making under Generalized Linear Model with High-Dimensional Data, arXiv:1812.02962v1, p. 18, Proposition 4 (hypotheses from Lemma EC.9, p. ec18)

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret

universe u

/-- **Proposition 4** (p. 18; proof: Lemma EC.9, p. ec18). Under A.1, A.3, A.4 and A.5, for every
`a > 2304 s/(p* κ)` there are constants `C₀ ≥ max{10, 16/p*}` and `C₅ > 0` such that, when the
G-MCP-Bandit runs with `t₀ = 2C₀|𝒦|` and `λ_{1,0} = C₅`, for every `T ≥ max{(t₀+1)²/e² − 1, e}` and
every `k ∈ 𝒦_o` the random-sample MCP estimator `β^random_k(T)` (2sWL with `λ₁(T)` on `ℛ_k(T)`)
satisfies `ℙ(‖β^random_k(T) − β_k‖₁ ≤ min{1/(σ₂x_max), h/(4eσ₂R_max x_max)}) ≥ 1 − 15/(T+1)`. -/
theorem proposition_4 {d K : ℕ} (hd : 1 ≤ d) (hK : 2 ≤ K)
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (xmax s Rmax βmin b h pstar κ σ σ2 σ3 : ℝ) (Ko Ks : Finset (Fin K))
    (hglm : IsGLMFamily ν g Rmax)
    (hA1 : A1 𝒳 β xmax s Rmax βmin b)
    (hA3 : A3 𝒳 PX ν g β Ko Ks h pstar)
    (hA4 : A4 𝒳 PX ν g β Ko h s b κ)
    (hA5 : A5 g Rmax b xmax σ σ2 σ3) :
    ∀ a : ℝ, 2304 * s / (pstar * κ) < a →
    ∃ C0 C5 : ℝ, 10 ≤ C0 ∧ 16 / pstar ≤ C0 ∧ 0 < C5 ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K),
      IsPrimitives P 𝒳 PX ν g β Rmax X R V A →
    ∀ sel : WLSelector d, IsWLSelector g Rmax b sel →
    ∀ T : ℕ, max ((2 * C0 * K + 1) ^ 2 / Real.exp 1 ^ 2 - 1) (Real.exp 1) ≤ (T : ℝ) →
    ∀ k ∈ Ko,
      ENNReal.ofReal (1 - 15 / ((T : ℝ) + 1)) ≤
        P {ω | l1 (betaRandom sel (2 * C0 * K) C5 a X R V A k T ω - β k) ≤
          min (1 / (σ2 * xmax)) (h / (4 * Real.exp 1 * σ2 * Rmax * xmax))} := by sorry

end GMCPBandit.Regret
