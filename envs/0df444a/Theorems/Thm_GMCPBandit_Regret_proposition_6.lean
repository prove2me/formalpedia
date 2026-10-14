-- Prove2me | Theorems.Thm_GMCPBandit_Regret_proposition_6
-- name    : GMCPBandit.Regret.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:39.450075+00:00
-- url     : https://prove2.me/theorems/fdc339fe-a975-45b3-8b7b-76c92e3c140b
-- title:
--   Proposition 6, p. 19 — ℙ(‖β^whole(T) − β^true‖₂ ≤ √(C_β s²/(T+1))) ≥ 1 − 13/(T+1)
-- statement:
--   Work in the model of §3 under Assumptions A.1, A.3, A.4 and A.5, and let $a>2304s/(p^*\kappa)$. There are constants $C_0\ge10$, $C_4,C_5,C_\beta>0$ and $T_0$ such that the following holds when the G-MCP-Bandit runs with $t_0=2C_0|\mathcal K|$, the margin $h$ of A.3, $\lambda_{1,0}=C_5$, $\lambda_{2,0}=C_4$ and $a$. For every 2sWL selection rule, every tie-breaking rule, every $T\ge T_0$ and every optimal decision $k\in\mathcal K_o$, the whole-sample MCP estimator $\beta^{whole}_k(T)$ (the 2sWL estimate on all samples of $k$ up to $T$ with $\lambda_2(T)$) satisfies
--   $$\mathbb P\Big(\|\beta^{whole}_k(T)-\beta^{true}_k\|_2\le\sqrt{C_\beta\frac{s^2}{T+1}}\Big)\ge1-\frac{13}{T+1}.$$
--
--   Although the whole-sample data are collected adaptively and are not i.i.d., the whole-sample estimator converges at the parametric rate $s/\sqrt T$; this drives the lower level of the bi-level decision.
--
--   **Formalization Note** The proposition names neither the algorithm's parameters nor a threshold on $T$; they become the existential constants $C_0,C_4,C_5,T_0$, and $C_\beta$ is existential too. All are placed before the probability space, the selection and tie-breaking rules and $T$; a $T$-dependent $C_\beta$ would make the claim free, since every estimate lies in $B_b$. The statement is for $k\in\mathcal K_o$. The selection and tie-breaking rules are measurable, so the trajectory is a random variable.
-- source:
--   Wang, Wei and Yao, Online Learning and Decision-Making under Generalized Linear Model with High-Dimensional Data, arXiv:1812.02962v1, p. 19, Proposition 6

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret

universe u

/-- **Proposition 6** (p. 19). Under A.1, A.3, A.4 and A.5, for every `a > 2304 s/(p* κ)` there are
constants `C₀ ≥ 10`, `C₄, C₅, C_β > 0` and `T₀` such that, when the G-MCP-Bandit runs with
`t₀ = 2C₀|𝒦|`, `h` (A.3), `λ_{1,0} = C₅`, `λ_{2,0} = C₄` and `a`, for every 2sWL selection rule, every
tie-breaking rule, every `T ≥ T₀` and every `k ∈ 𝒦_o`, the whole-sample MCP estimator satisfies
`ℙ(‖β^whole_k(T) − β_k‖₂ ≤ √(C_β s²/(T+1))) ≥ 1 − 13/(T+1)`. -/
theorem proposition_6 {d K : ℕ} [NeZero K] (hd : 1 ≤ d) (hK : 2 ≤ K)
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (xmax s Rmax βmin b h pstar κ σ σ2 σ3 : ℝ) (Ko Ks : Finset (Fin K))
    (hglm : IsGLMFamily ν g Rmax)
    (hA1 : A1 𝒳 β xmax s Rmax βmin b)
    (hA3 : A3 𝒳 PX ν g β Ko Ks h pstar)
    (hA4 : A4 𝒳 PX ν g β Ko h s b κ)
    (hA5 : A5 g Rmax b xmax σ σ2 σ3) :
    ∀ a : ℝ, 2304 * s / (pstar * κ) < a →
    ∃ C0 C4 C5 Cβ T0 : ℝ, 10 ≤ C0 ∧ 0 < C4 ∧ 0 < C5 ∧ 0 < Cβ ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K),
      IsPrimitives P 𝒳 PX ν g β Rmax X R V A →
    ∀ sel : WLSelector d, IsWLSelector g Rmax b sel →
    ∀ tb : ArgmaxRule K, IsArgmaxRule tb →
    ∀ T : ℕ, T0 ≤ (T : ℝ) →
    ∀ k ∈ Ko,
      ENNReal.ofReal (1 - 13 / ((T : ℝ) + 1)) ≤
        P {ω | l2 (betaWhole ν g sel tb ⟨2 * C0 * K, h, C5, C4, a⟩ X R V A k T ω - β k) ≤
          Real.sqrt (Cβ * s ^ 2 / ((T : ℝ) + 1))} := by sorry

end GMCPBandit.Regret
