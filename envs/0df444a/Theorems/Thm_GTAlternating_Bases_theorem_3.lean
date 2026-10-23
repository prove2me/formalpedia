-- Prove2me | Theorems.Thm_GTAlternating_Bases_theorem_3
-- name    : GTAlternating.Bases.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:18.808983+00:00
-- url     : https://prove2.me/theorems/8315e8cb-54ed-432a-b7ac-d3d5c6291667
-- title:
--   Theorem 3, p. 12 — the class of a path α̲ in S̃(α) has 2^{r+1} elements, r = number of branchings from self-conjugate to non-self-conjugate
-- statement:
--   Let $\underline\alpha = (\alpha^{(2)},\dots,\alpha^{(n)})$ be a sequence in $\tilde{\mathcal S}(\alpha^{(n)})$. Its class consists of all sequences $\underline\beta = (\beta^{(2)},\dots,\beta^{(n)})$ that are themselves paths ($\beta^{(i)} \in (\beta^{(i+1)})^\dagger$, $\beta^{(2)} \in \tilde\Theta(2)$) with $\beta^{(i)} \sim \alpha^{(i)}$ for all $i$; the last entry may be $\alpha^{(n)}$ or, for non-self-conjugate $\alpha^{(n)}$, its conjugate. Then the class has exactly
--   $$2^{r+1}$$
--   elements, where
--   $$r = \#\{2 \le i < n \mid \alpha^{(i)} = \mu^{\pm} \text{ for some } \mu = \mu', \text{ and } \alpha^{(i+1)} = \lambda \text{ for some } \lambda \ne \lambda'\}.$$
--
--   This count is why one representative per class, all ending at the same $\alpha$, is needed in the Main Theorem.
--
--   **Formalization Note.** The class is counted with `Set.encard`, so the statement also asserts that it is finite. Paths are stored top-down; `branchCount` counts consecutive pairs (non-self-conjugate above, self-conjugate below). The first sentence of Theorem 3 (the bijection $\bar\Gamma : \mathcal S(\alpha) \to \mathrm{geo}(\alpha)$) is not stated.
-- source:
--   Geetha, Prasad, Comparison of Gelfand-Tsetlin bases for alternating and symmetric groups, arXiv:1606.04424v2, p. 12, Theorem 3 (cardinality clause)

import Mathlib
import Definitions.Def_GTAlternating_Bases_Model

namespace GTAlternating.Bases

theorem theorem_3 (a : Label) (p : List Label) (hp : IsPath a p) :
    Set.encard {l : List Label | (∃ c q, l = c :: q ∧ IsPath c q) ∧
        List.Forall₂ Label.Equiv l (a :: p)} = 2 ^ (branchCount (a :: p) + 1) := by sorry

end GTAlternating.Bases
