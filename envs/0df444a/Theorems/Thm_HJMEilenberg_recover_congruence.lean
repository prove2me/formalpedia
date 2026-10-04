-- Prove2me | Theorems.Thm_HJMEilenberg_recover_congruence
-- name    : HJMEilenberg.recover_congruence
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-09T10:44:45.988871+00:00
-- url     : https://prove2.me/theorems/0ca1f3da-2edd-4f50-a177-24ba6105f356
-- title:
--   Congruence-formation recovery identity
-- statement:
--   Let $S$ be finite, let $\mathfrak F$ be a finite-index congruence formation, and let $\mathcal L$ be a regular-language formation that agrees at every variable family with the saturation construction $\mathcal L_{\mathfrak F}$. Then applying the language-to-congruence construction recovers the original formation pointwise:
--
--   $$
--   \mathfrak F_{\mathcal L}(X)=\mathfrak F(X)
--   \qquad\text{for every sorted variable family $X$.}
--   $$
--
--   This is the first inverse identity in the final formation isomorphism.
-- source:
--   Juan Climent Vidal and Enric Cosme Llópez, Eilenberg theorems for many-sorted formations, Houston Journal of Mathematics 45(2) (2019), Section 6, pp. 351–416; arXiv:1604.04792. The free-term substrate is cross-checked against the companion TeX source A Kleene theorem for free many-sorted algebras. Section 6, first recovery identity in the proof of the final formation-isomorphism proposition.

import Definitions.Def_HJMEilenberg_Formations

namespace HJMEilenberg

open MSKleene

/-- First recovery identity in Proposition 6.23. -/
theorem recover_congruence {S : Type} [Finite S] {sig : Signature S}
    (F : FiniteIndexCongruenceFormation sig)
    (L : RegularLanguageFormation sig)
    (hL : ∀ X : SSet S, L.languages X = languagesOf F X) :
    ∀ X : SSet S, congruencesOf L X = F.congruences X := by
  sorry

end HJMEilenberg
