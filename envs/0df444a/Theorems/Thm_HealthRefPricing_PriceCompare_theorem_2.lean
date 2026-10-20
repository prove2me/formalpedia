-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_theorem_2
-- name    : HealthRefPricing.PriceCompare.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:35.996239+00:00
-- url     : https://prove2.me/theorems/8e90fda2-e560-40bb-9af1-7a9f8ed4ed2b
-- title:
--   Theorem 2, p. 13 (PDF 14) — given the non-value-based set 𝒩, the RP equilibrium prices are the unique solution of the FOC system
-- statement:
--   Consider the two-provider model under reference pricing, under the standing assumptions and Assumption 2. Write $S^{RP}_j(P)$ for provider $j$'s market share when the out-of-pocket costs are $o_k = \tilde c + \max\{0, p_k - p^*\}$. Then:
--
--   1. a Nash equilibrium of the reference-pricing price game exists;
--   2. if $P = (p_1,p_2)$ is such an equilibrium and $\mathcal N = \{j : p_j > p^*\}$ is its set of non-value-based providers, then $P$ solves the system
--   $$1 - \gamma(p_j - c)\bigl(1 - S^{RP}_j(P)\bigr) = 0 \quad \forall j \in \mathcal N, \qquad p_i = p^* \quad \forall i \notin \mathcal N;$$
--   3. $P$ is the only solution $Q = (q_1,q_2)$ of this system with $q_j > p^*$ for every $j \in \mathcal N$.
--
--   Theorem 2 lets one compute the RP equilibrium once the set of non-value-based providers is known; Algorithm 1 of the paper and Proposition 3 then determine that set.
--
--   **Formalization Note** Provider $j$ ranges over `Fin 2`, index `0` being the paper's provider 1. "Consider as given the set $\mathcal N$" is read as: $\mathcal N$ is the non-value-based set of the equilibrium, and uniqueness is among profiles that price above $p^*$ exactly on $\mathcal N$ and at $p^*$ off it; the statement makes no claim about solutions of the system with a different status pattern. Part 1 (existence) is not in the theorem's sentence but is established in its proof (Appendix p. 6, "Therefore, there exists a Nash equilibrium") and is included so that hypotheses of the form "$P$ is an RP equilibrium" elsewhere in the mission are not vacuous.
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), p. 13 (PDF 14), Theorem 2; existence from its proof, Appendix pp. 5–6 (PDF 38–39)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Theorem 2 (p. 13), with the existence of an equilibrium from its proof (Appendix p. 6):
an RP equilibrium exists, and every RP equilibrium `p`, with non-value-based set
`𝒩 = {j | p* < p_j}`, solves the system `1 - γ(p_j - c)(1 - S^{RP}_j) = 0` on `𝒩`,
`p_i = p*` off `𝒩`, and is the only solution of that system that prices above `p*` on `𝒩`. -/
theorem theorem_2 (P : Params) (hS : P.Standing) (hA2 : Assumption2 P) :
    (∃ p : Fin 2 → ℝ, IsEqRP P p) ∧
      ∀ p : Fin 2 → ℝ, IsEqRP P p →
        (∀ j, P.ps < p j → 1 - P.γ * (p j - P.c) * (1 - share P (oopRP P p) j) = 0) ∧
        (∀ i, ¬ P.ps < p i → p i = P.ps) ∧
        ∀ q : Fin 2 → ℝ,
          (∀ j, P.ps < p j →
            P.ps < q j ∧ 1 - P.γ * (q j - P.c) * (1 - share P (oopRP P q) j) = 0) →
          (∀ i, ¬ P.ps < p i → q i = P.ps) → q = p := by sorry

end HealthRefPricing.PriceCompare
