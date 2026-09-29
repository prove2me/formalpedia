-- Prove2me | Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top
-- name    : IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/07452e33-4134-5fd1-83d5-517cf39aad15
-- title:
--   Zariski gluing of compatible elements over a finite basic cover
-- statement:
--   Let $R$ be a commutative ring, $M$ an $R$-module, and $\iota$ a finite index type. Given a family $g : \iota \to R$ whose range generates the unit ideal, i.e. $\mathrm{Ideal.span}(\mathrm{range}\,g) = \top$, suppose given: $R$-modules $N_i$ together with $R$-linear maps $f_i : M \to N_i$ each exhibiting $N_i$ as the localisation of $M$ at the submonoid of powers of $g_i$ (in the sense of `IsLocalizedModule (Submonoid.powers (g i)) (f i)`); $R$-modules $N_{2,ij}$ for each pair $(i,j)$ together with $R$-linear maps $l_{ij} : N_i \to N_{2,ij}$ each exhibiting $N_{2,ij}$ as the localisation of $N_i$ at the powers of $g_j$; and further $R$-linear maps $l'_{ij} : N_j \to N_{2,ij}$, with no localisation hypothesis on the $l'_{ij}$, subject to the compatibility $l_{ij} \circ f_i = l'_{ij} \circ f_j$ as linear maps $M \to N_{2,ij}$ for all $i,j$. Then for every family $x$ with $x_i \in N_i$ satisfying $l_{ij}(x_i) = l'_{ij}(x_j)$ for all $i,j$, there exists $m \in M$ with $f_i(m) = x_i$ for every $i$. Note that $M$, the $N_i$ and the $N_{2,ij}$ are constrained to lie in a common universe.
--
--   This is the module-theoretic heart of Zariski gluing over a finite cover of $\operatorname{Spec} R$ by basic open sets $D(g_i)$: a family of sections of the localisations $M_{g_i}$ agreeing on the overlaps $D(g_i) \cap D(g_j)$ is the restriction of a global element of $M$. The hypotheses are in the one-step shape delivered by restriction maps of quasi-coherent module data, and the result is used in the treatment of presheaves of $\mathcal{O}$-modules, in particular for quasi-coherence statements and for constructions of morphisms out of affine pieces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type w} [Fintype ι] (g : ι → R) (hg : Ideal.span (Set.range g) = ⊤)
    {N : ι → Type v} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (f i)]
    {N₂ : ι → ι → Type v} [∀ i j, AddCommGroup (N₂ i j)] [∀ i j, Module R (N₂ i j)]
    (l : ∀ i j, N i →ₗ[R] N₂ i j) [∀ i j, IsLocalizedModule (Submonoid.powers (g j)) (l i j)]
    (l' : ∀ i j, N j →ₗ[R] N₂ i j) (hll : ∀ i j, l i j ∘ₗ f i = l' i j ∘ₗ f j)
    (x : ∀ i, N i) (hx : ∀ i j, l i j (x i) = l' i j (x j)) :
    ∃ m : M, ∀ i, f i m = x i := by sorry
