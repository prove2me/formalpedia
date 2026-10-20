-- Prove2me | Theorems.Thm_HealthRefPricing_PriceCompare_theorem_1
-- name    : HealthRefPricing.PriceCompare.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:23:36.540899+00:00
-- url     : https://prove2.me/theorems/c5214892-de8b-48f8-8dc4-e3f51958e673
-- title:
--   Theorem 1, p. 12 (PDF 13) — the VP equilibrium prices are the unique solution of the FOC system (5)
-- statement:
--   Consider the two-provider model under variable payment with cost share $\lambda \in (0,1]$, under the standing assumptions and Assumption 1 at $\lambda$. Write $S^{VP}_j(P)$ for provider $j$'s market share when the out-of-pocket costs are $o_k = \lambda p_k$. Then the system of first-order conditions
--
--   $$1 - \gamma\lambda(p_j - c)\bigl(1 - S^{VP}_j(P)\bigr) = 0, \qquad j = 1,2, \tag{5}$$
--
--   has exactly one solution $P = (p_1, p_2)$, and a price vector is a Nash equilibrium of the VP price game if and only if it solves (5). In particular, a VP equilibrium exists and is unique.
--
--   The theorem reduces the equilibrium of the VP game to a two-equation system, which is what the comparative statics in the cost share (Lemma 2) and the comparison with reference pricing (Proposition 5) work with.
--
--   **Formalization Note** Provider $j$ ranges over `Fin 2`, index `0` being the paper's provider 1. Equilibrium is a pure Nash equilibrium over prices in $\mathbb R$ (see the Model definition).
-- source:
--   Nassiri, Adida & Mamani, Reference pricing for healthcare services, author manuscript (SSRN 3176280, version of Dec. 28, 2020; eScholarship 3sm502rz), p. 12 (PDF 13), Theorem 1, eq. (5); proof Appendix pp. 4–5 (PDF 37–38)

import Mathlib
import Definitions.Def_HealthRefPricing_PriceCompare_Model

namespace HealthRefPricing.PriceCompare

/-- Theorem 1 (p. 12): under Assumption 1, the first-order system (5) has exactly one solution,
and the variable-payment equilibria are exactly its solutions. -/
theorem theorem_1 (P : Params) (hS : P.Standing) (lam : ℝ) (hlam : lam ∈ Set.Ioc (0 : ℝ) 1)
    (hA1 : Assumption1 P lam) :
    (∃! p : Fin 2 → ℝ, ∀ j, 1 - P.γ * lam * (p j - P.c) * (1 - share P (oopVP lam p) j) = 0) ∧
      ∀ p : Fin 2 → ℝ, IsEqVP P lam p ↔
        ∀ j, 1 - P.γ * lam * (p j - P.c) * (1 - share P (oopVP lam p) j) = 0 := by sorry

end HealthRefPricing.PriceCompare
