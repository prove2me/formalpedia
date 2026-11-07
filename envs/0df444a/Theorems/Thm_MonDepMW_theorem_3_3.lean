-- Prove2me | Theorems.Thm_MonDepMW_theorem_3_3
-- name    : MonDepMW.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:42.037706+00:00
-- url     : https://prove2.me/theorems/d0926ee9-c2ce-453d-aace-22ff5efb32b8
-- title:
--   Theorem 3.3 — almost linear neighborhood complexity
-- statement:
--   For every monadically dependent graph class $\mathcal C$ there is a function $\gamma$ with $\gamma(n)\leqslant\mathrm{subpoly}_{\mathcal C}(n)$ such that for any $G\in\mathcal C$ and non-empty $A\subseteq V(G)$,
--   $$|\mathcal T_1(G,A)|\leqslant\gamma(|A|)\cdot|A|.$$
--
--   This theorem of Dreier et al. [13] is the deep combinatorial input of the mission.
--
--   Differences from the source:
--   - encoding: a graph class → GraphClass, members on each Fin n, no isomorphism closure; reason: every finite graph has a copy on some Fin n, and all quantities are isomorphism invariant
--   - encoding: γ : N → N with γ(n) ⩽ subpoly(n) → γ : ℕ → ℕ with Subpolynomial γ; reason: a function bounded by a subpolynomial function is itself subpolynomial (squeeze), and conversely; N is the positive integers; the value at 0 is not constrained by the limit and enters only on the empty graph, where every bound holds, or not at all
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Theorem 3.3, p.13

import Mathlib
import Definitions.Def_MonDepMW_Subpolynomial
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_MonDepMW_oneType

set_option autoImplicit false

namespace MonDepMW

/-- **Theorem 3.3.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.13 ([13, Theorem 2]): "For every monadically dependent graph class C, there is a function
γ : N → N with γ(n) ⩽ subpoly_C(n) such that for any graph G ∈ C and non-empty set A ⊆ V (G), we have
|𝒯1(G, A)| ⩽ γ(|A|) · |A|." -/
theorem theorem_3_3 (𝒞 : GraphClass) (h𝒞 : MonadicallyDependent 𝒞) :
    ∃ γ : ℕ → ℕ, Subpolynomial γ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∀ A : Finset (Fin n), A.Nonempty →
        numParts (oneType G A) ≤ γ A.card * A.card := by sorry

end MonDepMW
