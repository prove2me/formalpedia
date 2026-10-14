-- Prove2me | Theorems.Thm_MFIrrev_Equilibrium_proposition_4_3
-- name    : MFIrrev.Equilibrium.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:30.581308+00:00
-- url     : https://prove2.me/theorems/a513b517-41a8-40f0-87f1-02641650158d
-- title:
--   Proposition 4.3 (with (4.18) corrected), p. 16 — V(x,i) = kᵢ + ∫_{aᵢ}^x v(y,i)dy and the barrier control (4.11) is optimal
-- statement:
--   Assume the standing conditions of §2 and Assumption 2.1, and fix $Q\in(0,\infty)^2$. Let $v$ be the value of the stopping problem (4.13) and $a_1,a_2>0$ its thresholds as in Proposition 4.2, i.e. $v(x,i)<\kappa\iff x>a_i$ for $x>0$. Let $k_1,k_2$ solve the linear system
--   $$\begin{cases}-(\rho+p_1)k_1+p_1k_2+\big(\eta_1-\delta\kappa\big)a_1-ca_1^2-p_1\displaystyle\int_{a_1}^{a_2}v(y,2)\,dy=0,\\[4pt] p_2k_1-(\rho+p_2)k_2+\big(\eta_2-\delta\kappa\big)a_2-ca_2^2+p_2\displaystyle\int_{a_1}^{a_2}v(y,1)\,dy=0.\end{cases}$$
--   Then for every $x>0$ and regime $i$, the barrier control (4.11) at $(a_1,a_2)$ is admissible and optimal, and the value function of the singular control problem is
--   $$V(x,i)=k_i+\int_{a_i}^xv(y,i)\,dy.$$
--
--   This links the stopping problem to the singular control problem: the marginal value of capacity is $v$.
--
--   **Formalization Note (correction).** The page prints the term $(\eta_i-\delta a_i\kappa)a_i$; the proof (Appendix A, (A.15)–(A.17)) produces $(\eta_i-\delta\kappa)a_i$, and the printed term is dimensionally inconsistent with the others, so the corrected system is used. The system has determinant $\rho^2+\rho(p_1+p_2)>0$, so $k$ is unique. "$V$ satisfies (4.19)" is stated as attainment by the barrier control plus domination of every admissible payoff. Regimes are `Fin 2` (index `0` = regime 1); $\int_{a_1}^{a_2}$ is the oriented integral. The barriers are taken positive because (4.11) contains $\ln(a_{\varepsilon_s}/x)$.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, p. 16, Proposition 4.3, (4.18) corrected, (4.19); proof in Appendix A, p. 28

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_StoppingProblem

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MFIrrev.Equilibrium

/-- Proposition 4.3 (with (4.18) corrected), Aïd–Basei–Ferrari p. 16. Regime index `0` is the paper's
regime 1. Let `a_j > 0` be the thresholds of Proposition 4.2 and `k` solve the linear system (4.18)
with the term `(η_i − δκ)a_i` (the page prints `(η_i − δa_iκ)a_i`). Then for every `x > 0` and regime
`i`, the barrier control (4.11) is admissible and optimal, with value
`V(x, i) = k_i + ∫_{a_i}^x v(y, i) dy` ((4.19)). -/
theorem proposition_4_3 (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j) (hp : ∀ j, 0 < m.p j ∧ m.p j < 1)
    (hρ : 0 < m.ρ) (hc : 0 < m.c) (hκ : 0 < m.κ) (hφ : ∀ j, 0 < m.φ j) (hζ : ∀ j, 0 < m.ζ j)
    (hα0 : 0 < m.α) (hα1 : m.α < 1) (hφρδ : ∀ j, m.ρ + m.δ < m.φ j)
    (hA21 : 2 * max (m.σ 0 ^ 2) (m.σ 1 ^ 2) < m.ρ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Setting Ω) (hS : IsSetting m P S)
    (Q : Fin 2 → ℝ) (hQ : ∀ j, 0 < Q j)
    (a : Fin 2 → ℝ) (ha : ∀ j, 0 < a j)
    (hreg : ∀ j, ∀ y : ℝ, 0 < y → (vStop m P S Q y j < m.κ ↔ a j < y))
    (k : Fin 2 → ℝ)
    (h418_1 : -(m.ρ + m.p 0) * k 0 + m.p 0 * k 1 + (eta m Q 0 - m.δ * m.κ) * a 0 - m.c * a 0 ^ 2
      - m.p 0 * ∫ y in (a 0)..(a 1), vStop m P S Q y 1 = 0)
    (h418_2 : m.p 1 * k 0 - (m.ρ + m.p 1) * k 1 + (eta m Q 1 - m.δ * m.κ) * a 1 - m.c * a 1 ^ 2
      + m.p 1 * ∫ y in (a 0)..(a 1), vStop m P S Q y 0 = 0) :
    ∀ x : ℝ, 0 < x → ∀ i : Fin 2,
      IsAdmissible m P S x i (barrier m S a x) ∧
      J m P S x i Q (barrier m S a x) = k i + ∫ y in (a i)..x, vStop m P S Q y i ∧
      ∀ I, IsAdmissible m P S x i I →
        J m P S x i Q I ≤ k i + ∫ y in (a i)..x, vStop m P S Q y i := by sorry

end MFIrrev.Equilibrium
