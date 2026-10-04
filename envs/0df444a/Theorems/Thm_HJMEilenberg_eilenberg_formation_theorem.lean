-- Prove2me | Theorems.Thm_HJMEilenberg_eilenberg_formation_theorem
-- name    : HJMEilenberg.eilenberg_formation_theorem
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-09T10:45:08.198486+00:00
-- url     : https://prove2.me/theorems/9ce03425-deff-498a-8431-20844e78029f
-- title:
--   Eilenberg theorem for many-sorted formations
-- statement:
--   Let $S$ be finite and $\Sigma$ an $S$-sorted signature. There exists an order isomorphism
--
--   $$
--   \operatorname{Form}_{\mathrm{Cgr}_{\mathrm{fi}}}(\Sigma)
--   \simeq_o
--   \operatorname{Form}_{\mathrm{Lang}_{r}}(\Sigma)
--   $$
--
--   from finite-index congruence formations to regular-language formations. For every congruence formation $\mathfrak F$, its image selects exactly the languages saturated by some congruence in $\mathfrak F$; for every language formation $\mathcal L$, the inverse image selects exactly the finite-index congruences all of whose saturated languages lie in $\mathcal L$.
--
--   The displayed pointwise equalities fix the order isomorphism to be the two constructions of the paper, rather than an arbitrary equivalence between the underlying ordered types.
-- source:
--   Juan Climent Vidal and Enric Cosme Llópez, Eilenberg theorems for many-sorted formations, Houston Journal of Mathematics 45(2) (2019), Section 6, pp. 351–416; arXiv:1604.04792. The free-term substrate is cross-checked against the companion TeX source A Kleene theorem for free many-sorted algebras. Section 6, final proposition: the complete lattices of finite-index congruence formations and regular-language formations are isomorphic.

import Definitions.Def_HJMEilenberg_Formations

namespace HJMEilenberg

open MSKleene

/-- Proposition 6.23: the complete lattices of finite-index congruence
formations and regular-language formations are isomorphic. The displayed
equalities fix the isomorphism to be exactly the two maps defined in the
paper. -/
theorem eilenberg_formation_theorem {S : Type} [Finite S]
    (sig : Signature S) :
    ∃ e : FiniteIndexCongruenceFormation sig ≃o
        RegularLanguageFormation sig,
      (∀ (F : FiniteIndexCongruenceFormation sig) (X : SSet S),
        (e F).languages X = languagesOf F X) ∧
      (∀ (L : RegularLanguageFormation sig) (X : SSet S),
        (e.symm L).congruences X = congruencesOf L X) := by
  sorry

end HJMEilenberg
