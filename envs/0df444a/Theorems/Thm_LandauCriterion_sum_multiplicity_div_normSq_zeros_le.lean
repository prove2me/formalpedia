-- Prove2me | Theorems.Thm_LandauCriterion_sum_multiplicity_div_normSq_zeros_le
-- name    : LandauCriterion.sum_multiplicity_div_normSq_zeros_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-20T23:53:31.316826+00:00
-- url     : https://prove2.me/theorems/3fd28325-6f10-4141-b879-a33dbc6a2cf7
-- title:
--   Under RH, $\sum_{\rho} m_\rho/|\rho|^2 \le 2+\gamma-\log 4\pi$ over nontrivial zeros
-- statement:
--   Assume the Riemann hypothesis. Let $Z$ be a finite set of zeros $\rho$ of the Riemann zeta function $\zeta$ with $\operatorname{Re}\rho>0$ (that is, nontrivial zeros), and for each $\rho$ let $m_\rho$ be its multiplicity as a zero of $\zeta$. Then
--
--   $$
--   \sum_{\rho\in Z}\frac{m_\rho}{|\rho|^2}\;\le\;2+\gamma-\log(4\pi),
--   $$
--
--   where $\gamma$ is the Euler–Mascheroni constant ($2+\gamma-\log 4\pi\approx 0.0462$).
--
--   Under RH one has $|\rho|^2=\rho(1-\rho)$ for every nontrivial zero, and the constant $2+\gamma-\log 4\pi$ equals $\sum_\rho\frac{1}{\rho(1-\rho)}=2\sum_\rho\operatorname{Re}\frac1\rho$, the sum over all nontrivial zeros counted with multiplicity; so the bound is sharp. It controls, with an explicit leading constant, the sum over zeros in the explicit formula for the Riesz mean $\psi_1(x)=\sum_{n\le x}\Lambda(n)(x-n)$, which is what the Massias–Nicolas–Robin criterion for Landau's function requires.
--
--   **Formalization Note** The multiplicity $m_\rho$ is `analyticOrderNatAt riemannZeta ρ`; $|\rho|$ is the complex norm. Since $\zeta(1)\neq0$, the condition excludes $\rho=1$.
-- source:
--   H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74 (Springer, 2000), Chapter 12: the constant B in the Hadamard product of ξ satisfies B = −Σ_ρ Re(1/ρ) and B = −γ/2 − 1 + (1/2) log 4π; under RH, Re(1/ρ) = 1/(2|ρ|²), so Σ_ρ m_ρ/|ρ|² = 2 + γ − log 4π. Auxiliary lemma for the formal proof of the criterion of J.-P. Massias, J.-L. Nicolas, G. Robin, "Évaluation asymptotique de l'ordre maximum d'un élément du groupe symétrique", Acta Arith. 50 (1988), 221–242; as quoted in Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), sentence "The statement that ln g(n) < sqrt(Li^{-1}(n)) for all sufficiently large n is equivalent to the Riemann hypothesis".

import Mathlib

namespace LandauCriterion
theorem sum_multiplicity_div_normSq_zeros_le (hRH : RiemannHypothesis) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ 0 < ρ.re) :
    ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 ≤
      2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by sorry
end LandauCriterion
