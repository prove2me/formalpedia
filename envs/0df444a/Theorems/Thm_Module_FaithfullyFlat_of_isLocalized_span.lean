-- Prove2me | Theorems.Thm_Module_FaithfullyFlat_of_isLocalized_span
-- name    : Module.FaithfullyFlat.of_isLocalized_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/4afd1af0-788a-5c39-99d6-52c1b6509dd2
-- title:
--   Faithful flatness is local on the base
-- statement:
--   Let $R$ be a commutative ring and let $s \subseteq R$ be a subset whose generated ideal is all of $R$, i.e. $\mathrm{span}(s) = \top$. Let $M$ be an $R$-module. For each $r \in s$ let $R_r$ be a commutative $R$-algebra which is a localisation of $R$ away from $r$ (a localisation at the submonoid of powers of $r$), let $M_r$ be a module over both $R_r$ and $R$ with compatible scalar actions (an $R$-$R_r$ scalar tower), and let $g_r \colon M \to M_r$ be an $R$-linear map exhibiting $M_r$ as the localisation of $M$ away from $r$. Assume that for every $r \in s$ the module $M_r$ is faithfully flat over $R_r$. The conclusion is that $M$ is faithfully flat over $R$. The indexing is over the subtype of elements of $s$, so the localising element attached to an index $r$ is its underlying element of $R$.
--
--   This is the statement that faithful flatness, like flatness, is Zariski-local on the base: faithful flatness over a covering family of basic opens $\mathrm{Spec}\,R_r$, $r \in s$ with $s$ generating the unit ideal, implies faithful flatness over $R$. It is used to assemble faithful flatness of a module over a base ring from its pieces along a decomposition of the base by idempotents, the application being [`HopfAlgebra.faithfullyFlat_hopfKer_of_finitePartIdempotent`](thm.html#HopfAlgebra.faithfullyFlat_hopfKer_of_finitePartIdempotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FaithfullyFlat_of_isLocalized_span.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false

theorem Module.FaithfullyFlat.of_isLocalized_span
    {R : Type*} [CommRing R] (s : Set R) (spn : Ideal.span s = ⊤)
    {M : Type*} [AddCommGroup M] [Module R M]
    (Rₛ : s → Type*) [∀ r : s, CommRing (Rₛ r)] [∀ r : s, Algebra R (Rₛ r)]
    [∀ r : s, IsLocalization.Away r.1 (Rₛ r)]
    (Mₛ : s → Type*) [∀ r : s, AddCommGroup (Mₛ r)] [∀ r : s, Module R (Mₛ r)] [∀ r : s, Module (Rₛ r) (Mₛ r)]
    [∀ r : s, IsScalarTower R (Rₛ r) (Mₛ r)]
    (g : ∀ r : s, M →ₗ[R] Mₛ r) [∀ r : s, IsLocalizedModule.Away r.1 (g r)]
    (H : ∀ r : s, Module.FaithfullyFlat (Rₛ r) (Mₛ r)) :
    Module.FaithfullyFlat R M := by sorry
