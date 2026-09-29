-- Prove2me | Theorems.Thm_M4aHerbrand_exists_res_ideles_iso_res_mulEquiv_fixedField
-- name    : M4aHerbrand.exists_res_ideles_iso_res_mulEquiv_fixedField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/f3c5a9ba-c2b5-5bb5-b72a-51b44df439f0
-- title:
--   Restricting the idèle representation to a subgroup
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, and let $D$ be idèle descent data for $F/E$, i.e. a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $\mathrm{Gal}(F/E) = (F \simeq_{\mathrm{alg}[E]} F)$ to the ring automorphisms of the adèle ring $\mathbb{A}_F$ of $F$ over $\mathcal{O}_F$, such that each $D.\mathrm{act}\,g$ is continuous and restricts along $F \to \mathbb{A}_F$ to $g$ on $F$. Assume $\mathrm{Gal}(F/E)$ acts multiplicatively on the idèle group $\mathbb{A}_F^{\times}$ by an action pinned by $hactI$ to be $g \cdot x = D.\mathrm{unitsAct}\,g\,x$, the automorphism of units induced by $D.\mathrm{act}\,g$. Let $S \le \mathrm{Gal}(F/E)$ be a subgroup, let $D'$ be idèle descent data for $F$ over the fixed field $F^{S}$, with a multiplicative action of $(F \simeq_{\mathrm{alg}[F^{S}]} F)$ on $\mathbb{A}_F^{\times}$ pinned in the same way to $D'$, and let $\iota : S \simeq^{*} (F \simeq_{\mathrm{alg}[F^{S}]} F)$ be a group isomorphism such that $\iota(s)$ acts on $F$ as $s$ does. Then there is an isomorphism $e$ of $S$-representations between the restriction along $S \hookrightarrow \mathrm{Gal}(F/E)$ of the $\mathrm{Gal}(F/E)$-representation on $\mathrm{Additive}\,\mathbb{A}_F^{\times}$ and the restriction along $\iota$ of the corresponding $(F \simeq_{\mathrm{alg}[F^{S}]} F)$-representation, whose underlying maps in both directions are the identity on elements.
--
--   This records the standard identification of the idèle group of $F$ as a module over $H \le \mathrm{Gal}(F/E)$ with the idèle group of $F$ viewed as a $\mathrm{Gal}(F/F^{H})$-module, in the form of an isomorphism of representations that is literally the identity on idèles, so that value-pinned coordinate maps transport unchanged. It is used in the semilocal (Shapiro) computation of the cohomology of the idèles, where statements for $F/E$ restricted to $H$ are read off from the extension $F/F^{H}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_res_ideles_iso_res_mulEquiv_fixedField.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem M4aHerbrand.exists_res_ideles_iso_res_mulEquiv_fixedField
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : F ≃ₐ[E] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (S : Subgroup (F ≃ₐ[E] F))
    (D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField S) F)
    [MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI' : ∀ (g : F ≃ₐ[IntermediateField.fixedField S] F) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D'.unitsAct g x)
    (ι : S ≃* (F ≃ₐ[IntermediateField.fixedField S] F))
    (hι : ∀ (s : S) (x : F), ι s x = (s : F ≃ₐ[E] F) x) :
    ∃ e : Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ≅
        Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (AdeleRing (𝓞 F) F)ˣ),
      (∀ x, e.hom.hom x = x) ∧ (∀ x, e.inv.hom x = x) := by sorry
