-- Prove2me | Theorems.Thm_HJMEilenberg_recover_languages
-- name    : HJMEilenberg.recover_languages
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-09T10:44:56.012616+00:00
-- url     : https://prove2.me/theorems/6dae11f1-1f28-4992-a2b1-b6c2956fcfd0
-- title:
--   Regular-language-formation recovery identity
-- statement:
--   Let $S$ be finite, let $\mathcal L$ be a regular-language formation, and let $\mathfrak F$ be a finite-index congruence formation that agrees at every variable family with the construction $\mathfrak F_{\mathcal L}$. Then applying the congruence-to-language construction recovers the original formation pointwise:
--
--   $$
--   \mathcal L_{\mathfrak F}(X)=\mathcal L(X)
--   \qquad\text{for every sorted variable family $X$.}
--   $$
--
--   This is the second inverse identity in the final formation isomorphism.
-- source:
--   Juan Climent Vidal and Enric Cosme Llópez, Eilenberg theorems for many-sorted formations, Houston Journal of Mathematics 45(2) (2019), Section 6, pp. 351–416; arXiv:1604.04792. The free-term substrate is cross-checked against the companion TeX source A Kleene theorem for free many-sorted algebras. Section 6, second recovery identity in the proof of the final formation-isomorphism proposition.

import Definitions.Def_HJMEilenberg_Formations

namespace HJMEilenberg

open MSKleene

/-- Second recovery identity in Proposition 6.23. -/
theorem recover_languages {S : Type} [Finite S] {sig : Signature S}
    (L : RegularLanguageFormation sig)
    (F : FiniteIndexCongruenceFormation sig)
    (hF : ∀ X : SSet S, F.congruences X = congruencesOf L X) :
    ∀ X : SSet S, languagesOf F X = L.languages X := by
  sorry

end HJMEilenberg
