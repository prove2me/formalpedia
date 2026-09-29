-- Prove2me | Theorems.Thm_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq
-- name    : NumberField.PlaceTransport.exists_bijective_doubleCoset_decomp_of_under_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/a1d7b5fa-5ace-528f-8fda-eb8fec3c4bef
-- title:
--   Places above v in F^H and double cosets D_wbackslash G/H
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, write $G = F \simeq_{\mathrm{alg}[E]} F$ for its Galois group, let $H \le G$ be a subgroup with fixed field $F^H$, let $v$ be a height one prime of $\mathcal{O}_E$ and $w$ a height one prime of $\mathcal{O}_F$ whose contraction $w \cap \mathcal{O}_E$ equals $v$. Let $\iota$ denote the subtype of height one primes $v'$ of $\mathcal{O}_{F^H}$ with $v' \cap \mathcal{O}_E = v$, and let $D_w =$ [`NumberField.PlaceDecomp.decomp E F w`](def/NumberField_PlaceDecompositionAction.html#L82) be the decomposition subgroup of $G$ at the valuation subring of the $w$-adic valuation of $F$. The assertion is that $\iota$ is finite, and that there is a map $g : \iota \to G$ such that: (i) $i \mapsto D_w\, g(i)\, H$ is a bijection from $\iota$ onto the set of double cosets of $D_w$ and $H$ in $G$; (ii) some $i_0 \in \iota$ has underlying prime $w \cap \mathcal{O}_{F^H}$ and $g(i_0) = 1$; (iii) for every $i$, the prime $g(i)^{-1} \cdot w$ of $\mathcal{O}_F$ contracts to $i$ in $\mathcal{O}_{F^H}$; (iv) for every $i$ there is $h \in H$ with $h \cdot \mathrm{above}(F^H, F, i) = g(i)^{-1} \cdot w$, where $\mathrm{above}$ is the chosen prime of $\mathcal{O}_F$ over the given prime of $\mathcal{O}_{F^H}$; and (v) for every $i$, the subgroup $g(i) H g(i)^{-1} \cap D_w$ and the subgroup $H \cap D_{\mathrm{above}(F^H, F, i)}$ have the same cardinality, the latter decomposition subgroup again being taken in $G$.
--
--   This is the classical dictionary between the primes of an intermediate field $F^H$ above $v$ and the double cosets $D_w \backslash G / H$, obtained from transitivity of $G$ on the primes of $F$ above $v$ together with the identification of the stabiliser of $w$ with its decomposition group, in the explicit form (a choice of double coset representatives $g(i)$, normalised so that the prime $w \cap F^H$ corresponds to the identity, together with the matching of intersection orders) needed downstream. It feeds the double coset (Mackey) computation [`M4aHerbrand.finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp`](thm.html#M4aHerbrand.finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp), where local contributions of a corestricted global class are compared over decomposition subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq.lean

import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceAbove

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open IsDedekindDomain NumberField
open scoped NumberField.PlaceTransport Pointwise

theorem NumberField.PlaceTransport.exists_bijective_doubleCoset_decomp_of_under_eq
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (H : Subgroup (F ≃ₐ[E] F)) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v) :
    Finite {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v} ∧
    ∃ g : {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v} → (F ≃ₐ[E] F),
      Function.Bijective (fun i => DoubleCoset.mk (NumberField.PlaceDecomp.decomp E F w) H (g i)) ∧
      (∃ i₀, i₀.1 = w.under (𝓞 ↥(IntermediateField.fixedField H)) ∧ g i₀ = 1) ∧
      (∀ i, ((g i)⁻¹ • w).under (𝓞 ↥(IntermediateField.fixedField H)) = i.1) ∧
      (∀ i, ∃ h : ↥H, (h : F ≃ₐ[E] F) • NumberField.PlaceAbove.above (↥(IntermediateField.fixedField H)) F i.1 = (g i)⁻¹ • w) ∧
      (∀ i, Nat.card ↥((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) =
        Nat.card ↥(H ⊓ NumberField.PlaceDecomp.decomp E F
          (NumberField.PlaceAbove.above (↥(IntermediateField.fixedField H)) F i.1))) := by sorry
