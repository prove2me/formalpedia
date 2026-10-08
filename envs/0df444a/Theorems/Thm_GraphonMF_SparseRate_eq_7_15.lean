-- Prove2me | Theorems.Thm_GraphonMF_SparseRate_eq_7_15
-- name    : GraphonMF.SparseRate.eq_7_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:05.93398+00:00
-- url     : https://prove2.me/theorems/810ad278-e01a-425d-b705-30d27831116e
-- title:
--   (7.15), p. 3615 — R^{n,2}_s ≤ (κ/n) Σⱼ 𝔼|Xⁿ_j(s) − X_{j/n}(s)|² + κ(q)/(nβₙ)^{1/q} (under Condition 4.3)
-- statement:
--   Fix the setting of the mission: Condition 4.1, a graphon $G$, edges $\xi^n_{ij}$ satisfying Condition 4.3, Condition 2.3 for $\mu(0)$ and $G$, and a solution $X$ of the limit system (4.2). For a solution $(X^n_i)_{i\le n}$ of (4.1) and $s\in[0,T]$ let
--   $$R^{n,2}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\frac{\xi^n_{ij}}{\beta_n}\big(b(X_{i/n}(s),X^n_j(s))-b(X_{i/n}(s),X_{j/n}(s))\big)\Big|^2 .$$
--   There is a constant $\kappa$ such that for every $q\in(1,\infty)$ there is a constant $\kappa(q)$ such that for every $n$, every solution $(X^n_i)$ of (4.1) and every $s\in[0,T]$,
--   $$R^{n,2}_s\le\frac{\kappa}{n}\sum_{j=1}^n\mathbb E\big|X^n_j(s)-X_{j/n}(s)\big|^2+\frac{\kappa(q)}{(n\beta_n)^{1/q}} .$$
--
--   This is the key estimate of the paper's §7: it bounds the interaction error by the coupling error itself plus a term that vanishes as $n\beta_n\to\infty$, which closes the Gronwall argument for Theorems 4.1 and 4.2.
--
--   **Formalization Note** Proved in §7.1 under Condition 4.2; §7.3 (p. 3616) states that it still holds under Conditions 2.3, 4.1 and 4.3. It is stated here under exactly those conditions. $\kappa$ does not depend on $q$ (it comes from (7.6)); $\kappa(q)$ is chosen after $q$; both are chosen before $n$ and $s$. $|\cdot|$ is the sup norm of $\mathbb R^d$; expectations are lower Lebesgue integrals.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3615, (7.15); validity under Condition 4.3: p. 3616, §7.3

import Mathlib
import Definitions.Def_GraphonMF_SparseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.SparseRate

/-- (7.15) (p. 3615), under Conditions 2.3, 4.1 and 4.3 (§7.3, p. 3616): there is `κ` such that for each `q > 1`,
`R^{n,2}_s ≤ (κ/n) Σ_j 𝔼|Xⁿ_j(s) − X_{j/n}(s)|² + κ(q)/(nβ_n)^{1/q}`. -/
theorem eq_7_15 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {β : ℕ → ℝ} (h41 : Cond41 μ0 b σ β) {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G)
    {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ} (h43 : Cond43 P X0 B ξ β G)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X)
    {N : ℕ} {J : Fin N → Set I} (h23 : Cond23 μ0 G J) :
    ∃ κ : ℝ, ∀ q : ℝ, 1 < q → ∃ κq : ℝ, ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ),
      IsParticleSolution41 P hN h43.meas T b σ β n Xn → ∀ s : ℝ≥0, s ≤ T →
        Rn2 P b β ξ X n Xn s ≤
          ENNReal.ofReal (κ / n) * ∑ j : Fin n, ∫⁻ ω, ‖Xn j s ω - X (GraphonMF.DenseRate.lab n j) s ω‖ₑ ^ 2 ∂P +
            ENNReal.ofReal (κq / ((n : ℝ) * β n) ^ (1 / q)) := by sorry

end GraphonMF.SparseRate
