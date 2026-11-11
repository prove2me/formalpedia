-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40
-- name    : GaussLocalMaxColoring.Main.lemma_40
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:21:58.192728+00:00
-- url     : https://prove2.me/theorems/8088a8e1-83a1-422a-99d1-5afb1bb24ff4
-- title:
--   Lemma 40 — computer-verified parameters $(a,b,\mu,c,\kappa,\theta)$ for Cases 1 and 2
-- statement:
--   Let $1.968\le A\le A_0$ and $\rho\in[-\tfrac12,1)$. In Case 1 ($q_A(\rho)<q_c(\rho)$; $L=q_A(\rho)/\sqrt{1-\rho^2}$, $J=C_{D_a}(\rho)+\tfrac14$, $\Lambda=1$) and in Case 2 ($\rho=-\tfrac12$; $L=A$, $J=D_a+\tfrac14$, $\Lambda=3999/1000$) there exist $(a,b,\mu,c,\kappa,\theta)$, independent of $\rho'$, such that (i) $a,\mu,c,\kappa\ge0$, $b\in\mathbb R$, $0<\theta<14$; (ii) $a^2+b^2+\mu^2\le1-10^{-12}$ and $c^2+\kappa^2\le\tfrac14-10^{-20}$; (iii) $L^2+\Lambda(\mu+\theta(\mu+\kappa))^2\ge J+10^{-18}$; (iv) for every $\rho'$ with $-\tfrac12\le\rho'\le\tfrac12-\rho$ and $\tfrac34-\rho^2-\rho'^2-\rho\rho'\ge0$,
--   $$\frac{L(1/2+\rho\rho')-(1+\theta)b(\rho'+\rho/2)+\theta c|\rho'+\rho/2|}{\sqrt{1-\rho^2}}+\tfrac32(1+\theta)a-\tfrac{\sqrt3}2\theta A\ge q_A(\rho')+3\cdot10^{-6}.$$
--   Moreover $L>0$ in both cases. The paper verifies this by computation (Appendix C).
--
--   Differences from the source: none.
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 40, printed p. 42 (PDF 44); Appendix C (pp. 72–77, PDF 74–79)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Section5

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 40** (p. 42, PDF 44; verified by computation in Appendix C). Let
`1.968 ≤ A ≤ A₀` and `ρ ∈ [−1/2, 1)`. In Case 1 (`q_A(ρ) < q_c(ρ)`; `L = q_A(ρ)/√(1−ρ²)`,
`J = C_{D_a}(ρ) + 1/4`, `Λ = 1`) and in Case 2 (`ρ = −1/2`; `L = A`, `J = D_a + 1/4`,
`Λ = 3999/1000`) there exist `(a, b, μ, c, κ, θ)`, independent of `ρ′`, satisfying (i)–(iv);
moreover `L > 0` in both cases. -/
theorem lemma_40 (A ρ : ℝ) (hA1 : 1968 / 1000 ≤ A) (hA2 : A ≤ A0) (hρ1 : -(1 / 2) ≤ ρ)
    (hρ2 : ρ < 1) :
    (qA A ρ < qc ρ →
      (∃ a b μ c κ θ : ℝ, L40Case1 A ρ a b μ c κ θ) ∧ 0 < qA A ρ / Real.sqrt (1 - ρ ^ 2)) ∧
    (ρ = -(1 / 2) → (∃ a b μ c κ θ : ℝ, L40Case2 A a b μ c κ θ) ∧ 0 < A) := by sorry

end GaussLocalMaxColoring.Main
