-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_proposition_5
-- name    : HealthRefPricing.PriceCompare.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:41.097982+00:00
-- url     : https://prove2.me/theorems/b040c6c9-e6d7-4c96-a04c-373deeee6eed
-- title:
--   Proposition 5, p. 18 (PDF 19) — provider j prices higher under variable payment than under reference pricing iff λ < λ∗_j
-- statement:
--   Consider the two-provider model under the standing assumptions ($m > 0$, $\gamma > 0$, $a_1 \le a_2$, $\tilde c < c$), with Assumption 1 at every cost share $\lambda \in (0,1]$, Assumption 2, and a co-payment below the reference price, $\tilde c < p^*$. Let $P^{RP} = (p^{RP}_1, p^{RP}_2)$ be a Nash equilibrium of the reference-pricing price game, and fix a provider $j$. Then there exists a threshold $\lambda^*_j \in (0,1]$ such that for every cost share $\lambda \in (0,1]$ and every Nash equilibrium $P^{VP}(\lambda)$ of the variable-payment price game at $\lambda$,
--
--   $$p^{VP}_j(\lambda) > p^{RP}_j \iff \lambda < \lambda^*_j .$$
--
--   Reference pricing does not depend on $\lambda$. The proposition says that variable payment leads to higher provider prices than reference pricing exactly when the patient cost share is low, and to lower prices once the cost share passes a provider-specific threshold.
--
--   **Formalization Note** Providers are indexed by `Fin 2`: index `0` is the paper's provider 1 and index `1` is provider 2. The equivalence is required of every VP equilibrium at every $\lambda$, so no equilibrium selection is assumed (Theorem 1 makes it unique). Two hypotheses are added to the page's sentence and disclosed: $\tilde c < p^*$, which the paper's proof uses ("knowing that $\tilde c < p^*$") and without which the statement fails (with $p^* < \tilde c$ numerical instances have the VP price above the RP price even at $\lambda = 1$); and Assumption 1 at every $\lambda \in (0,1]$, since the paper states Assumption 1 for the cost share under consideration and the proposition ranges over all of them. The proposition is stated about Nash equilibria of the two price games, not about solutions of the first-order systems.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), p. 18 (PDF 19), Proposition 5; proof Appendix pp. 9–10 (PDF 42–43)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Proposition 5 (p. 18): for each provider `j` there is `λ*_j ∈ (0,1]` such that, for every cost
share `λ ∈ (0,1]`, provider `j` prices higher at the variable-payment equilibrium than at the
reference-pricing equilibrium iff `λ < λ*_j`. -/
theorem proposition_5 (P : Params) (hS : P.Standing)
    (hA1 : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, Assumption1 P lam) (hA2 : Assumption2 P)
    (hct : P.ct < P.ps) (pRP : Fin 2 → ℝ) (hRP : IsEqRP P pRP) (j : Fin 2) :
    ∃ lamStar ∈ Set.Ioc (0 : ℝ) 1, ∀ lam ∈ Set.Ioc (0 : ℝ) 1, ∀ p : Fin 2 → ℝ, IsEqVP P lam p →
      (pRP j < p j ↔ lam < lamStar) := by sorry

end HealthRefPricing.PriceCompare
