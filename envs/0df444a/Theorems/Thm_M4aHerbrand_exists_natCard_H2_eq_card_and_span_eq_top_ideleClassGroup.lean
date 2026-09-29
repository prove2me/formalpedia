-- Prove2me | Theorems.Thm_M4aHerbrand_exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup
-- name    : M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/c69f2478-ebfa-53b6-b261-56a875bd6b7f
-- title:
--   H²(Gal(F/E), C_F) is cyclic of order |G|
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an extension of $E$ that is Galois, and write $G = F \simeq_{\mathrm{alg}[E]} F$ for its automorphism group. Let $D$ be an idèle Galois descent datum for $F/E$, that is, a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $G$ to the ring automorphisms of the adèle ring $\mathrm{AdeleRing}\,(\mathcal{O}_F)\,F$, such that each $D.\mathrm{act}\,g$ is continuous and commutes with $g$ under the structure map $F \to \mathrm{AdeleRing}\,(\mathcal{O}_F)\,F$. The idèle class group $C_F = \mathrm{IdeleClassGroup}\,(\mathcal{O}_F)\,F$ is the quotient of the unit group of the adèle ring by the subgroup of principal idèles, i.e. the image of $F^\times$ under the unit map of $F \to \mathrm{AdeleRing}\,(\mathcal{O}_F)\,F$; assume $G$ acts on $C_F$ by group automorphisms in such a way that the action of each $g$ coincides with $D.\mathrm{classAct}\,g$, the automorphism of the quotient induced by $D.\mathrm{act}\,g$ on units. Regard $C_F$ as the $\mathbb{Z}$-linear representation of $G$ attached to this multiplicative action. Then there is a class $u$ in $H^2(G, C_F)$ such that the cardinality of $H^2(G, C_F)$ equals the cardinality of $G$, and the $\mathbb{Z}$-submodule spanned by $\{u\}$ is all of $H^2(G, C_F)$. Thus $H^2(G, C_F)$ is cyclic of order $|G| = [F:E]$, the identification of $|G|$ with the degree not being part of the Lean statement.
--
--   This is the top layer of the construction of the global fundamental class: combined with the vanishing of $H^1$ for all subgroups and the bound $\#H^2 \le |G|$, it pins down $H^2(\mathrm{Gal}(F/E), C_F)$ as cyclic of order exactly $[F:E]$. It is used to produce a distinguished generator of $H^2$, in [`M4aHerbrand.exists_fundamentalClass_ideleClassGroup`](thm.html#M4aHerbrand.exists_fundamentalClass_ideleClassGroup) and in its refinement recording the image of that generator under restriction-type maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∃ u : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2,
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)
          = Nat.card (F ≃ₐ[E] F) ∧
      Submodule.span ℤ {u} = ⊤ := by sorry
