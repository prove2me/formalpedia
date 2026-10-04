-- Prove2me | Theorems.Thm_HJMEilenberg_languages_to_congruences
-- name    : HJMEilenberg.languages_to_congruences
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-09T10:44:35.642594+00:00
-- url     : https://prove2.me/theorems/f2976edd-13ce-4e08-a3e8-b230cdce3d81
-- title:
--   Regular-language formations yield congruence formations
-- statement:
--   Let $S$ be finite and let $\mathcal L$ be a regular-language formation for an $S$-sorted signature $\Sigma$. There exists a finite-index congruence formation $\mathfrak F$ whose congruences over every sorted variable family $X$ are exactly
--
--   $$
--   \mathfrak F(X)=\mathfrak F_{\mathcal L}(X)
--   =\{\Phi\mid \text{$\Phi$ has finite index and every $\Phi$-saturated language belongs to $\mathcal L(X)$}\}.
--   $$
--
--   This states that the paper's language-to-congruence construction satisfies all finite-index congruence formation axioms.
-- source:
--   Juan Climent Vidal and Enric Cosme Llópez, Eilenberg theorems for many-sorted formations, Houston Journal of Mathematics 45(2) (2019), Section 6, pp. 351–416; arXiv:1604.04792. The free-term substrate is cross-checked against the companion TeX source A Kleene theorem for free many-sorted algebras. Section 6, Proposition Lang2CongEnFinit.

import Definitions.Def_HJMEilenberg_Formations

namespace HJMEilenberg

open MSKleene

/-- Proposition 6.22: a regular-language formation determines a formation of
finite-index congruences by requiring all saturated languages. -/
theorem languages_to_congruences {S : Type} [Finite S] {sig : Signature S}
    (L : RegularLanguageFormation sig) :
    ∃ F : FiniteIndexCongruenceFormation sig,
      ∀ X : SSet S, F.congruences X = congruencesOf L X := by
  sorry

end HJMEilenberg
