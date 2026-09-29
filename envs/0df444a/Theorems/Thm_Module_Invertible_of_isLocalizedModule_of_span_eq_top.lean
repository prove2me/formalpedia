-- Prove2me | Theorems.Thm_Module_Invertible_of_isLocalizedModule_of_span_eq_top
-- name    : Module.Invertible.of_isLocalizedModule_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/3558711e-5295-55e0-9cda-73e6fd3f38b8
-- title:
--   Invertibility of a module is Zariski-local
-- statement:
--   Let $R$ be a commutative ring and $M$ an $R$-module, and let $s \subseteq R$ be a subset generating the unit ideal, $\mathrm{span}_R(s) = \top$. Suppose given, for each element $g$ of $s$, a commutative $R$-algebra $R_g$ which is a localisation of $R$ away from $g$ (i.e. at the powers of $g$), an $R$-module $M_g$ carrying a compatible $R_g$-module structure (a scalar tower $R \to R_g \to M_g$), and an $R$-linear map $\varphi_g : M \to M_g$ exhibiting $M_g$ as the localisation of $M$ at the submonoid of powers of $g$. Assume that for every $g \in s$ the $R_g$-module $M_g$ is invertible in Mathlib's sense, that is, the contraction map $\mathrm{Hom}_{R_g}(M_g, R_g) \otimes_{R_g} M_g \to R_g$ is bijective. The conclusion is that $M$ is an invertible $R$-module, i.e. the contraction map $\mathrm{Hom}_R(M,R) \otimes_R M \to R$ is bijective. The families of localisations are arbitrary models, keyed exactly as in the local-global criterion for finite presentation.
--
--   This is the statement that being an invertible module (finite projective of rank one, in the form 'the contraction map is bijective') is a Zariski-local property on the base, the direction complementary to the stability of invertibility under localisation and base change. It is used in the Čerednik–Drinfel'd material, through [`CerednikDrinfeld.FormalOmega.DeligneDatum.exists_forall_map_eq_of_span_eq_top`](thm.html#CerednikDrinfeld.FormalOmega.DeligneDatum.exists_forall_map_eq_of_span_eq_top), and is the source of the variant [`Module.Invertible.of_isLocalizedModule_of_span_range_eq_top`](thm.html#Module.Invertible.of_isLocalizedModule_of_span_range_eq_top) phrased for an indexed family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Invertible_of_isLocalizedModule_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

theorem Module.Invertible.of_isLocalizedModule_of_span_eq_top
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (s : Set R) (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type*} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : ∀ (g : s), Module.Invertible (Rₚ g) (Mₚ g)) :
    Module.Invertible R M := by sorry
