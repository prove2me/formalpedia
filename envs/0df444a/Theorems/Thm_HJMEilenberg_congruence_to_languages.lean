-- Prove2me | Theorems.Thm_HJMEilenberg_congruence_to_languages
-- name    : HJMEilenberg.congruence_to_languages
-- status  : Proved
-- author  : @Cosme
-- created : 2026-09-09T10:44:25.655695+00:00
-- url     : https://prove2.me/theorems/ee9c5687-424d-449e-ae89-db63b19aa9b6
-- title:
--   Congruence formations yield regular-language formations
-- statement:
--   Let $S$ be finite and let $\mathfrak F$ be a formation of finite-index congruences for an $S$-sorted signature $\Sigma$. There exists a regular-language formation $\mathcal L$ whose languages over every sorted variable family $X$ are exactly
--
--   $$
--   \mathcal L(X)=\mathcal L_{\mathfrak F}(X)
--   =\{L\mid \exists\Phi\in\mathfrak F(X),\ \text{$L$ is $\Phi$-saturated}\}.
--   $$
--
--   This states that the paper's congruence-to-language construction satisfies all regular-language formation axioms, with equality at every free algebra rather than only an abstract existence claim.
-- source:
--   Juan Climent Vidal and Enric Cosme Llópez, Eilenberg theorems for many-sorted formations, Houston Journal of Mathematics 45(2) (2019), Section 6, pp. 351–416; arXiv:1604.04792. The free-term substrate is cross-checked against the companion TeX source A Kleene theorem for free many-sorted algebras. Section 6, Proposition Cong2LangEnFinit, together with Proposition Cong2LangBasic.

import Definitions.Def_HJMEilenberg_Formations

namespace HJMEilenberg

open MSKleene

/-- Proposition 6.21: a finite-index congruence formation determines a
formation of regular languages by saturation. -/
theorem congruence_to_languages {S : Type} [Finite S] {sig : Signature S}
    (F : FiniteIndexCongruenceFormation sig) :
    ∃ L : RegularLanguageFormation sig,
      ∀ X : SSet S, L.languages X = languagesOf F X := by
  sorry

end HJMEilenberg
