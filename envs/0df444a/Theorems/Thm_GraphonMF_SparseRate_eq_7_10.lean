-- Prove2me | Theorems.Thm_GraphonMF_SparseRate_eq_7_10
-- name    : GraphonMF.SparseRate.eq_7_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:54.371971+00:00
-- url     : https://prove2.me/theorems/42239955-0bce-4718-9f50-c438376c979f
-- title:
--   (7.10), p. 3614 — 𝔼[ξⁿ_ij |Xⁿ_j(s) − X_{j/n}(s)|²] ≤ (2𝔼|Xⁿ_j(s) − X_{j/n}(s)|² + κ(q)/(nβₙ)^{1/q}) βₙ G(i/n, j/n)
-- statement:
--   Fix the setting of the mission: Condition 4.1, a graphon $G$, edges $\xi^n_{ij}$ satisfying Condition 4.3, Condition 2.3 for $\mu(0)$ and $G$, and a solution $X$ of the limit system (4.2). For every $q\in(1,\infty)$ there is a constant $\kappa(q)$ such that for every $n$, every solution $(X^n_i)_{i\le n}$ of (4.1), all $i,j\in\{1,\dots,n\}$ and all $s\in[0,T]$,
--   $$\mathbb E\big[\xi^n_{ij}\,|X^n_j(s)-X_{j/n}(s)|^2\big]\le\Big(2\,\mathbb E\big[|X^n_j(s)-X_{j/n}(s)|^2\big]+\frac{\kappa(q)}{(n\beta_n)^{1/q}}\Big)\,\beta_n\,G\big(\tfrac in,\tfrac jn\big).$$
--
--   The edge $\xi^n_{ij}$ influences the coupling error of particle $j$, so the two are not independent; the estimate says they are nearly so, up to the factor 2 and an error vanishing as $n\beta_n\to\infty$. It is one of the two inputs of (7.15).
--
--   **Formalization Note** The paper proves (7.10) in §7.1 under Condition 4.2, with $G_n(i/n,j/n)$; §7.3 (p. 3616) states that the estimates of §7.1 still hold under Conditions 2.3, 4.1 and 4.3, where the edge means are $\beta_nG(i/n,j/n)$, so $G$ replaces $G_n$ here and the statement carries those three conditions. The quantifier "for each $q>1$" is implicit on the page (the proof applies Hölder's inequality with exponents $p,q$); $\kappa(q)$ is chosen after $q$ and before $n,i,j,s$. The statement covers all $i,j$, including $i=j$, as the page ("Fix $i,j\in\{1,\dots,n\}$") does. $|\cdot|$ is the sup norm of $\mathbb R^d$; expectations are lower Lebesgue integrals.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3614, (7.10); validity under Condition 4.3: p. 3616, §7.3

import Mathlib
import Definitions.Def_GraphonMF_SparseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.SparseRate

/-- (7.10) (p. 3614), under Conditions 2.3, 4.1 and 4.3 (§7.3, p. 3616): for each `q > 1` there is `κ(q)` with
`𝔼[ξⁿ_ij |Xⁿ_j(s) − X_{j/n}(s)|²] ≤ (2𝔼|Xⁿ_j(s) − X_{j/n}(s)|² + κ(q)/(nβ_n)^{1/q}) β_n G(i/n, j/n)`. -/
theorem eq_7_10 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {β : ℕ → ℝ} (h41 : Cond41 μ0 b σ β) {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G)
    {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ} (h43 : Cond43 P X0 B ξ β G)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X)
    {N : ℕ} {J : Fin N → Set I} (h23 : Cond23 μ0 G J) :
    ∀ q : ℝ, 1 < q → ∃ κq : ℝ, ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ),
      IsParticleSolution41 P hN h43.meas T b σ β n Xn → ∀ (i j : Fin n) (s : ℝ≥0), s ≤ T →
        ∫⁻ ω, ENNReal.ofReal (ξ n ω i j) * ‖Xn j s ω - X (GraphonMF.DenseRate.lab n j) s ω‖ₑ ^ 2 ∂P ≤
          (2 * ∫⁻ ω, ‖Xn j s ω - X (GraphonMF.DenseRate.lab n j) s ω‖ₑ ^ 2 ∂P +
              ENNReal.ofReal (κq / ((n : ℝ) * β n) ^ (1 / q))) *
            ENNReal.ofReal (β n * G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j)) := by sorry

end GraphonMF.SparseRate
