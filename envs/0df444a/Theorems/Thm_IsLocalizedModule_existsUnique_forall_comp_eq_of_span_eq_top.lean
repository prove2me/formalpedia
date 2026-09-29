-- Prove2me | Theorems.Thm_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top
-- name    : IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/ddd151b4-1ebc-5c41-ad05-8d9967a7bb59
-- title:
--   Uniqueness of the Zariski glue of localised modules
-- statement:
--   Let $B$ be a commutative ring and let $f : \mathrm{Fin}\,k \to B$ be a finite family of elements generating the unit ideal, i.e. $\mathrm{span}(\mathrm{range}\,f) = \top$. Let $M_i$ ($i \in \mathrm{Fin}\,k$) and $M_{ij}$ ($i,j \in \mathrm{Fin}\,k$) be $B$-modules, and let $\rho^l_{ij} : M_i \to M_{ij}$ and $\rho^r_{ij} : M_j \to M_{ij}$ be $B$-linear maps such that each $\rho^r_{ij}$ exhibits $M_{ij}$ as the localisation of $M_j$ at the submonoid of powers of $f_i$; no such hypothesis is imposed on $\rho^l_{ij}$. Let $N$ be a $B$-module with $B$-linear maps $\pi_i : N \to M_i$, each exhibiting $M_i$ as the localisation of $N$ at the powers of $f_i$, and assume the overlap compatibility $\rho^l_{ij} \circ \pi_i = \rho^r_{ij} \circ \pi_j$ for all $i,j$. Then for every $B$-module $T$ and every family of $B$-linear maps $g_i : T \to M_i$ satisfying the same compatibility $\rho^l_{ij} \circ g_i = \rho^r_{ij} \circ g_j$ for all $i,j$, there is exactly one $B$-linear map $G : T \to N$ with $\pi_i \circ G = g_i$ for every $i$. All modules live in a single universe.
--
--   This is the universal property of a Zariski glue of a family of localisations: $(N, (\pi_i))$ is the limit of the diagram formed by the $M_i$ and the overlap maps, so any two glues of the same data are uniquely isomorphic and compatible families of chart maps glue uniquely. It is used in the construction of glued modules from a Drinfeld datum ([`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap)) and in [`LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart`](thm.html#LinearMap.exists_forall_localizedModule_mk_eq_of_forall_exists_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalizedModule_existsUnique_forall_comp_eq_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsLocalizedModule.existsUnique_forall_comp_eq_of_span_eq_top
    {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
    (M₂ : Fin k → Fin k → Type u) [∀ i j, AddCommGroup (M₂ i j)] [∀ i j, Module B (M₂ i j)]
    (ρl : ∀ i j, M i →ₗ[B] M₂ i j) (ρr : ∀ i j, M j →ₗ[B] M₂ i j)
    (hρr : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr i j))
    (N : Type u) [AddCommGroup N] [Module B N] (π : ∀ i, N →ₗ[B] M i)
    (hπ : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i))
    (hπc : ∀ i j, ρl i j ∘ₗ π i = ρr i j ∘ₗ π j)
    (T : Type u) [AddCommGroup T] [Module B T] (g : ∀ i, T →ₗ[B] M i)
    (hg : ∀ i j, ρl i j ∘ₗ g i = ρr i j ∘ₗ g j) :
    ∃! G : T →ₗ[B] N, ∀ i, π i ∘ₗ G = g i := by sorry
