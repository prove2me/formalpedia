-- Prove2me | Theorems.Thm_MonDepMW_lemma_5_1
-- name    : MonDepMW.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:55.853339+00:00
-- url     : https://prove2.me/theorems/14b87102-f462-4c98-a74c-bf008ad07988
-- title:
--   Lemma 5.1 — almost linear growth of $r$-types
-- statement:
--   For every monadically dependent graph class $\mathcal C$ and $r\geqslant1$ there is a function $\gamma_r$ with $\gamma_r(n)\leqslant\mathrm{subpoly}_{\mathcal C,r}(n)$ such that for any $G\in\mathcal C$ and non-empty $A\subseteq V(G)$,
--   $$|\mathcal T_r(G,A)|\leqslant\gamma_r(|A|)\cdot|A|.$$
--
--   It extends Theorem 3.3 to $r$-types.
--
--   Differences from the source:
--   - encoding: a graph class → GraphClass, members on each Fin n, no isomorphism closure; reason: every finite graph has a copy on some Fin n, and all quantities are isomorphism invariant
--   - encoding: γ_r : N → N with γ_r(n) ⩽ subpoly(n) → γ_r : ℕ → ℕ with Subpolynomial γ_r; reason: a function bounded by a subpolynomial function is itself subpolynomial (squeeze), and conversely; N is the positive integers; the value at 0 is not constrained by the limit and enters only on the empty graph, where every bound holds, or not at all
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Lemma 5.1, p.18

import Mathlib
import Definitions.Def_MonDepMW_Subpolynomial
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_MonDepMW_rType

set_option autoImplicit false

namespace MonDepMW

/-- **Lemma 5.1.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.18: "For every monadically dependent graph class C and r ∈ N, there is a function γr : N → N with
γr(n) ⩽ subpoly_{C,r}(n) such that for any graph G ∈ C and non-empty set A ⊆ V (G), we have |𝒯r(G, A)| ⩽ γr(|A|) · |A|." -/
theorem lemma_5_1 (𝒞 : GraphClass) (h𝒞 : MonadicallyDependent 𝒞) (r : ℕ) (hr : 1 ≤ r) :
    ∃ γ : ℕ → ℕ, Subpolynomial γ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∀ A : Finset (Fin n), A.Nonempty →
        numParts (rType G A r) ≤ γ A.card * A.card := by sorry

end MonDepMW
