-- Prove2me | Theorems.Thm_IsGalois_exists_units_quotientToInvariants_iso_res_apply_eq
-- name    : IsGalois.exists_units_quotientToInvariants_iso_res_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/df9f2def-5c29-5f94-a782-804f82ff0fa3
-- title:
--   Galois descent for unit groups, as representations
-- statement:
--   Let $E \subseteq L \subseteq M$ be fields, with $E$-algebra structures on $L$ and $M$ and an $L$-algebra structure on $M$ forming a scalar tower over $E$, and with $M/E$ finite and Galois. Suppose given multiplicative distributive actions of $\mathrm{Aut}_E(L)$ on $L^\times$ and of $\mathrm{Aut}_E(M)$ on $M^\times$ which are the tautological ones, in the sense that the hypotheses `hactL` and `hactM` require $(g \cdot a : L) = g(a)$ for all $g \in \mathrm{Aut}_E(L)$, $a \in L^\times$, and likewise over $M$. Let $S$ be a normal subgroup of $\mathrm{Aut}_E(M)$, let $\iota \colon \mathrm{Aut}_E(M)/S \xrightarrow{\ \sim\ } \mathrm{Aut}_E(L)$ be a group isomorphism, and assume the compatibility $\iota(gS)(y) = g(y)$ inside $M$ for all $g \in \mathrm{Aut}_E(M)$ and $y \in L$ (these hypotheses force $S$ to be exactly the subgroup of automorphisms fixing $L$ pointwise). The conclusion asserts the existence of an isomorphism $e$, in the category of $\mathbb{Z}$-linear representations of $\mathrm{Aut}_E(M)/S$, between the representation of $S$-invariants of the representation of $\mathrm{Aut}_E(M)$ on $\mathrm{Additive}\,M^\times$ and the restriction along $\iota$ of the representation of $\mathrm{Aut}_E(L)$ on $\mathrm{Additive}\,L^\times$, whose inverse is pinned down on elements: for every $a \in L^\times$, the underlying element of $M^\times$ of $e^{-1}(a)$ is the image of $a$ under the map $L^\times \to M^\times$ induced by the structure morphism $L \to M$.
--
--   This is the Galois correspondence $(M^\times)^{\mathrm{Gal}(M/L)} = L^\times$ for unit groups, packaged as an isomorphism of representations of the quotient group together with an explicit description of its inverse as the inclusion of unit groups. It feeds the inflation–restriction computation in degree two used by [`IsGalois.map_two_units_injective_and_exists_of_map_subtype_eq_zero`](thm.html#IsGalois.map_two_units_injective_and_exists_of_map_subtype_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsGalois_exists_units_quotientToInvariants_iso_res_apply_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem IsGalois.exists_units_quotientToInvariants_iso_res_apply_eq
    (E L M : Type) [Field E] [Field L] [Field M] [Algebra E L] [Algebra E M] [Algebra L M]
    [IsScalarTower E L M] [FiniteDimensional E M] [IsGalois E M]
    [MulDistribMulAction (L ≃ₐ[E] L) Lˣ]
    (hactL : ∀ (g : L ≃ₐ[E] L) (a : Lˣ), ((g • a : Lˣ) : L) = g (a : L))
    [MulDistribMulAction (M ≃ₐ[E] M) Mˣ]
    (hactM : ∀ (g : M ≃ₐ[E] M) (a : Mˣ), ((g • a : Mˣ) : M) = g (a : M))
    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (L ≃ₐ[E] L))
    (hι : ∀ (g : M ≃ₐ[E] M) (y : L), algebraMap L M (ι (QuotientGroup.mk g) y) = g (algebraMap L M y)) :
    ∃ e : (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ).quotientToInvariants S ≅
        Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction (L ≃ₐ[E] L) Lˣ),
      ∀ a : Lˣ, (e.inv.hom (Additive.ofMul a)).1 = Additive.ofMul (Units.map (algebraMap L M : L →* M) a) := by sorry
