-- Prove2me | Theorems.Thm_M4aHerbrand_unitIdelesTrivialOn_nonempty_res_iso_fixedField_and_groupCohomology_iso
-- name    : M4aHerbrand.unitIdelesTrivialOn.nonempty_res_iso_fixedField_and_groupCohomology_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/105e9980-f919-56ec-bfce-1eb035c8751a
-- title:
--   Unit idèles U_F^T as an H-module via the fixed field
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, let $D$ be an idèle Galois descent datum for $(\mathcal{O}_F, E, F)$, that is, a monoid homomorphism $g \mapsto D.\mathrm{act}(g)$ from $F \simeq_{\mathrm{alg}[E]} F$ to the ring automorphisms of the adèle ring $\mathbb{A}_F$, each continuous and compatible with $\mathrm{Gal}(F/E)$ acting on the image of $F$. Let $T$ be a set of height one primes of $\mathcal{O}_F$ and write $U =$ `unitIdelesTrivialOn (𝓞 F) F T` for the subgroup of $\mathbb{A}_F^\times$ consisting of those $x$ whose finite component at each $v \notin T$ lies, together with that of $x^{-1}$, in the valuation ring of the completion at $v$, whose infinite part is $1$, and whose finite component at each $w \in T$ is $1$. Assume $\mathrm{Gal}(F/E)$ acts on $U$ by group automorphisms, with the action pinned by the hypothesis that the image of $g \cdot x$ in $\mathbb{A}_F^\times$ equals $D.\mathrm{unitsAct}(g)(x)$. Let $H$ be a group, $f : H \to \mathrm{Gal}(F/E)$ a homomorphism, $E' =$ the fixed field of the image of $f$, let $D'$ be a descent datum for $(\mathcal{O}_F, E', F)$, assume $F \simeq_{\mathrm{alg}[E']} F$ acts on $U$ by group automorphisms pinned in the same way through $D'.\mathrm{unitsAct}$, and let $\iota : H \xrightarrow{\sim} F \simeq_{\mathrm{alg}[E']} F$ be a group isomorphism with $\iota(h)$ acting on $F$ as $f(h)$ does. Then there exists an isomorphism, in the category of $\mathbb{Z}$-linear representations of $H$, between the restriction along $f$ of $U$ (viewed additively via `Rep.ofMulDistribMulAction` for $\mathrm{Gal}(F/E)$) and the restriction along $\iota$ of $U$ with its $F \simeq_{\mathrm{alg}[E']} F$-action, and for every $n \in \mathbb{N}$ there exists an isomorphism $H^n(H, \mathrm{Res}_f U) \cong H^n(F \simeq_{\mathrm{alg}[E']} F, U)$. Only nonemptiness, that is the existence of such isomorphisms, is asserted.
--
--   This is the change-of-group comparison that replaces a group $H$ mapping to $\mathrm{Gal}(F/E)$ by the full Galois group of $F$ over the fixed field of its image, for the module of unit idèles trivial on $T$; it converts statements indexed by all such $H$ into statements about Galois groups of subextensions. It is used in the proof that the Tate cohomology of `unitIdelesTrivialOn` vanishes when all ramification indices equal one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_unitIdelesTrivialOn_nonempty_res_iso_fixedField_and_groupCohomology_iso.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand CategoryTheory

theorem M4aHerbrand.unitIdelesTrivialOn.nonempty_res_iso_fixedField_and_groupCohomology_iso
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F) (T : Set (HeightOneSpectrum (𝓞 F)))
    [MulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)]
    (hactU : ∀ (g : F ≃ₐ[E] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = D.unitsAct g x)
    (H : Type) [Group H] (f : H →* (F ≃ₐ[E] F))
    (D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField f.range) F)
    [MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField f.range] F) (unitIdelesTrivialOn (𝓞 F) F T)]
    (hactU' : ∀ (g : F ≃ₐ[IntermediateField.fixedField f.range] F) (x : unitIdelesTrivialOn (𝓞 F) F T),
      ((g • x : unitIdelesTrivialOn (𝓞 F) F T) : (AdeleRing (𝓞 F) F)ˣ) = D'.unitsAct g x)
    (ι : H ≃* (F ≃ₐ[IntermediateField.fixedField f.range] F))
    (hι : ∀ (h : H) (x : F), ι h x = f h x) :
    Nonempty (Rep.res f (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T)) ≅
        Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField f.range] F)
          (unitIdelesTrivialOn (𝓞 F) F T))) ∧
      ∀ n : ℕ, Nonempty (groupCohomology (Rep.res f
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (unitIdelesTrivialOn (𝓞 F) F T))) n ≅
        groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField f.range] F)
          (unitIdelesTrivialOn (𝓞 F) F T)) n) := by sorry
