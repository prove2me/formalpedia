-- Prove2me | Theorems.Thm_MFIrrev_Equilibrium_proposition_4_1
-- name    : MFIrrev.Equilibrium.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:32.575985+00:00
-- url     : https://prove2.me/theorems/0e16bb0d-f7d3-4245-a2ef-8da8fd83ba51
-- title:
--   Proposition 4.1, p. 14 — verification: a C² solution of the free-boundary problem (4.10) is the value function and the barrier control (4.11) is optimal
-- statement:
--   Assume the standing conditions of §2: $\delta,\sigma_i,\rho,c,\kappa,\varphi_i,\zeta_i>0$, $p_i\in(0,1)$, $0<\alpha<1$, $\min_i\varphi_i>\rho+\delta$, and Assumption 2.1, $\rho>2\max\{\sigma_1^2,\sigma_2^2\}$. Fix $Q\in(0,\infty)^2$ and let $\eta_i=\varphi_i+\zeta_iQ_i^{-\alpha}$.
--
--   Let $w:\mathbb R_+\times\{1,2\}\to\mathbb R$ be such that
--
--   1. for each $i$, $w(\cdot,i)\in C^2(\mathbb R_+)$ and $|w(x,i)|\le K(1+|x|^2)$ for some $K>0$ and all $x\ge0$;
--   2. there are $a_1,a_2>0$ with $\{(x,i): x>0,\ w'(x,i)<\kappa\}=\{(x,i): x>a_i\}$ (4.9);
--   3. $w$ solves the free-boundary problem (4.10): for $x>0$,
--   $$\begin{cases}(\mathcal L-\rho)w(x,i)+\eta_ix-cx^2\le0,& x<a_i,\\ (\mathcal L-\rho)w(x,i)+\eta_ix-cx^2=0,& x\ge a_i,\\ w'(x,i)-\kappa=0,& x\le a_i,\\ w'(x,i)-\kappa<0,& x>a_i.\end{cases}$$
--
--   Then for every initial state $(x,i)$ with $x>0$, the barrier control $I^\star$ of (4.11) at $(a_1,a_2)$ is admissible and
--   $$J_{(x,i)}(I^\star,Q)=w(x,i)\ \ge\ J_{(x,i)}(I,Q)\qquad\text{for every } I\in\mathcal A.$$
--   That is, the value function $V$ of the singular control problem equals $w$, and $I^\star$ is optimal.
--
--   This verification theorem turns the construction of the optimal investment policy into the analytic problem (4.10).
--
--   **Formalization Note.** Regimes are `Fin 2` (index `0` = regime 1). "$V\equiv w$" is stated as attainment by $I^\star$ plus domination of every admissible payoff, so no supremum over controls is formed. The barriers are taken positive (the page allows $(a_1,a_2)\in\mathbb R^2_+$, but (4.11) contains $\ln(a_{\varepsilon_s}/x)$). The conditions (4.9)–(4.10) are imposed at $x>0$, where the state lives, with the two-sided derivative; $C^2$ is on $[0,\infty)$.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, p. 14, Proposition 4.1, with (4.6), (4.9), (4.10), (4.11); proof in Appendix A

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_Model

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MFIrrev.Equilibrium

/-- Proposition 4.1 (verification theorem), Aïd–Basei–Ferrari p. 14. Regime index `0` is the
paper's regime 1. If `w` is `C²` on `[0, ∞)` in `x` with quadratic growth, `a` are positive
barriers with `{w' < κ} = {x > a_j}` ((4.9)), and `w` solves the free-boundary problem (4.10) for
`x > 0`, then for every `x > 0` and initial regime `i` the barrier control (4.11) is admissible,
attains `w(x, i)`, and no admissible control does better: `V ≡ w` and (4.11) is optimal. -/
theorem proposition_4_1 (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j) (hp : ∀ j, 0 < m.p j ∧ m.p j < 1)
    (hρ : 0 < m.ρ) (hc : 0 < m.c) (hκ : 0 < m.κ) (hφ : ∀ j, 0 < m.φ j) (hζ : ∀ j, 0 < m.ζ j)
    (hα0 : 0 < m.α) (hα1 : m.α < 1) (hφρδ : ∀ j, m.ρ + m.δ < m.φ j)
    (hA21 : 2 * max (m.σ 0 ^ 2) (m.σ 1 ^ 2) < m.ρ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Setting Ω) (hS : IsSetting m P S)
    (Q : Fin 2 → ℝ) (hQ : ∀ j, 0 < Q j)
    (w : ℝ → Fin 2 → ℝ)
    (hw_smooth : ∀ j, ContDiffOn ℝ 2 (fun y => w y j) (Ici 0))
    (hw_growth : ∃ K : ℝ, 0 < K ∧ ∀ j, ∀ y : ℝ, 0 ≤ y → |w y j| ≤ K * (1 + |y| ^ 2))
    (a : Fin 2 → ℝ) (ha : ∀ j, 0 < a j)
    (h49 : ∀ j, ∀ y : ℝ, 0 < y → (deriv (fun z => w z j) y < m.κ ↔ a j < y))
    (h410_1 : ∀ j, ∀ y : ℝ, 0 < y → y < a j →
      genL m w y j - m.ρ * w y j + eta m Q j * y - m.c * y ^ 2 ≤ 0)
    (h410_2 : ∀ j, ∀ y : ℝ, 0 < y → a j ≤ y →
      genL m w y j - m.ρ * w y j + eta m Q j * y - m.c * y ^ 2 = 0)
    (h410_3 : ∀ j, ∀ y : ℝ, 0 < y → y ≤ a j → deriv (fun z => w z j) y - m.κ = 0)
    (h410_4 : ∀ j, ∀ y : ℝ, 0 < y → a j < y → deriv (fun z => w z j) y - m.κ < 0) :
    ∀ x : ℝ, 0 < x → ∀ i : Fin 2,
      IsAdmissible m P S x i (barrier m S a x) ∧
      J m P S x i Q (barrier m S a x) = w x i ∧
      ∀ I, IsAdmissible m P S x i I → J m P S x i Q I ≤ w x i := by sorry

end MFIrrev.Equilibrium
