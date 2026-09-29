-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq
-- name    : NumberField.PlaceDecomp.exists_conj_and_transport_repHom_inf_decomp_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/a9508abf-ad8c-53e5-b9d6-00bf22f06a31
-- title:
--   Conjugation and transport for H-decomposition groups at conjugate places
-- statement:
--   Let $E$ and $F$ be fields with $F$ a number field and $F$ an $E$-algebra, let $H$ be a subgroup of $F \simeq_{\mathrm{alg}[E]} F$, let $w, w_1$ be height-one primes of $\mathcal{O}_F$, and let $h \in H$ satisfy $h \cdot w = w_1$ for the action on height-one primes. Write $D_v =$ `decomp E F v` for the decomposition subgroup of the valuation subring of the $v$-adic valuation of $F$ inside $F \simeq_{\mathrm{alg}[E]} F$. The assertion is twofold. First, $H \cap D_{w_1}$ and $H \cap D_w$ have the same cardinality (as `Nat.card`). Secondly, there exist a monoid homomorphism $c_h \colon H \cap D_{w_1} \to H \cap D_w$ and a morphism $T_h$ of representations from the restriction along $c_h$ of the representation of $H \cap D_w$ on the units $(F_w)^\times$ of the $w$-adic completion (obtained by restricting, along the inclusion $H \cap D_w \le D_w$, the natural multiplicative-distributive action representation `Rep.ofMulDistribMulAction`, written additively) to the corresponding representation of $H \cap D_{w_1}$ on $(F_{w_1})^\times$, such that: $c_h$ is bijective; $c_h(x) = h^{-1} x h$ in $F \simeq_{\mathrm{alg}[E]} F$ for every $x \in H \cap D_{w_1}$; and for every unit $x$ of $F_w$ the value of $T_h$ at $x$ equals [`NumberField.PlaceTransport.transport`](def/NumberField_PlaceTransport.html#L105) of $x$ along $h$ with respect to the hypothesis $h \cdot w = w_1$, as elements of $F_{w_1}$.
--
--   This is the statement that the decomposition groups of two places in the same orbit are conjugate, in the form needed for a fixed subgroup $H$: conjugation by $h$ matches $H \cap D_{w_1}$ with $H \cap D_w$ and the Galois transport of completions intertwines the two unit representations, with both the group isomorphism and the representation morphism pinned to their explicit values. It is used in the Herbrand-quotient computations, via [`M4aHerbrand.finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp`](thm.html#M4aHerbrand.finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp), to show that contributions of conjugate places agree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

theorem NumberField.PlaceDecomp.exists_conj_and_transport_repHom_inf_decomp_of_smul_eq
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (H : Subgroup (F ≃ₐ[E] F))
    (w w₁ : HeightOneSpectrum (𝓞 F)) (h : ↥H) (hh : (h : F ≃ₐ[E] F) • w = w₁) :
    Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) = Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w)) ∧
    ∃ (ch : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) →* ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w)))
      (Th : Rep.res ch (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)),
      Function.Bijective ch ∧
      (∀ x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)),
        ((ch x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w))) : F ≃ₐ[E] F) = (h : F ≃ₐ[E] F)⁻¹ * (x : F ≃ₐ[E] F) * (h : F ≃ₐ[E] F)) ∧
      (∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (Th.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
        NumberField.PlaceTransport.transport (h : F ≃ₐ[E] F) hh (x : w.adicCompletion F)) := by sorry
