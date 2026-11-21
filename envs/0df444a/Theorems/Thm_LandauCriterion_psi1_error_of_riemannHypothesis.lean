-- Prove2me | Theorems.Thm_LandauCriterion_psi1_error_of_riemannHypothesis
-- name    : LandauCriterion.psi1_error_of_riemannHypothesis
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-20T23:53:30.013916+00:00
-- url     : https://prove2.me/theorems/72955a89-0428-4e9d-9afc-0b50a10d96ff
-- title:
--   Under RH, $|\psi_1(x)-x^2/2|\le(2+\gamma-\log 4\pi)x^{3/2}+O(x^{5/4}\log^2 x)$
-- statement:
--   Let $\Lambda$ be the von Mangoldt function and let
--
--   $$
--   \psi_1(x)=\sum_{n\le x}\Lambda(n)\,(x-n)=\int_0^x\psi(t)\,dt
--   $$
--
--   be the first Riesz mean of $\Lambda$, where $\psi$ is Chebyshev's function. Assume the Riemann hypothesis. Then there is a constant $C>0$ such that for every real $x\ge 4$,
--
--   $$
--   \Bigl|\psi_1(x)-\frac{x^2}{2}\Bigr|\;\le\;(2+\gamma-\log 4\pi)\,x^{3/2}+C\,x^{5/4}\log^2 x,
--   $$
--
--   where $\gamma$ is the Euler–Mascheroni constant.
--
--   The leading constant $2+\gamma-\log 4\pi\approx 0.046$ is the value of $\sum_\rho|\rho|^{-2}$ over the nontrivial zeros under RH, and it is the size of the main term in the explicit formula $\psi_1(x)=\frac{x^2}{2}-\sum_\rho\frac{x^{\rho+1}}{\rho(\rho+1)}+O(x)$. An explicit constant of this quality is what makes the Massias–Nicolas–Robin criterion $\log g(n)<\sqrt{\mathrm{Li}^{-1}(n)}$ hold under RH.
--
--   **Formalization Note** $\psi_1(x)$ is written out as $\sum_{0\le n\le\lfloor x\rfloor}\Lambda(n)\max(x-n,0)$. The error term $Cx^{5/4}\log^2x$ is weaker than the classical $O(x)$ and suffices for the application.
-- source:
--   A. E. Ingham, The Distribution of Prime Numbers (Cambridge Tracts 30, 1932), Chapter IV (explicit formula for ψ₁(x) = ∫₀ˣ ψ(t) dt); H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74, Chapter 12 (B = −Σ_ρ Re(1/ρ) = −γ/2 − 1 + (1/2) log 4π). Auxiliary lemma for the formal proof of the criterion of J.-P. Massias, J.-L. Nicolas, G. Robin, "Évaluation asymptotique de l'ordre maximum d'un élément du groupe symétrique", Acta Arith. 50 (1988), 221–242; as quoted in Wikipedia, "Landau's function", revision oldid=1303222269 (https://en.wikipedia.org/w/index.php?title=Landau%27s_function&oldid=1303222269), sentence "The statement that ln g(n) < sqrt(Li^{-1}(n)) for all sufficiently large n is equivalent to the Riemann hypothesis".

import Mathlib

namespace LandauCriterion
theorem psi1_error_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 4 ≤ x →
      |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), ArithmeticFunction.vonMangoldt n * max (x - n) 0) -
          x ^ 2 / 2| ≤
        (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * x ^ (3 / 2 : ℝ) +
          C * (x ^ (5 / 4 : ℝ) * Real.log x ^ 2) := by sorry
end LandauCriterion
