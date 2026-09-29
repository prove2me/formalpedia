-- Prove2me | Theorems.Thm_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top
-- name    : IsLocalizedModule.existsUnique_forall_eq_of_span_range_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/9bb0090e-a2cf-5c8c-8cd6-1e25dc31a970
-- title:
--   Gluing elements of a module over a principal open cover
-- statement:
--   Let $R$ be a commutative ring, $M$ an $R$-module, $\iota$ a finite index type, and $g : \iota \to R$ a family whose range generates the unit ideal, $\mathrm{span}_R(\mathrm{range}\, g) = \top$. Suppose given $R$-modules $M_i$ for $i \in \iota$ and $R$-linear maps $f_i : M \to M_i$ each exhibiting $M_i$ as a localisation of $M$ at the submonoid of powers of $g_i$, and $R$-modules $M_{ij}$ for $i, j \in \iota$ with $R$-linear maps $f_{ij} : M \to M_{ij}$ each exhibiting $M_{ij}$ as a localisation of $M$ at the powers of $g_i g_j$. Suppose further given $R$-linear maps $\rho_{ij} : M_i \to M_{ij}$ and $\rho'_{ij} : M_j \to M_{ij}$ satisfying $\rho_{ij} \circ f_i = f_{ij}$ and $\rho'_{ij} \circ f_j = f_{ij}$ for all $i, j$. Then for every family $m = (m_i)_{i \in \iota}$ with $m_i \in M_i$ which is compatible on overlaps, in the sense that $\rho_{ij}(m_i) = \rho'_{ij}(m_j)$ for all $i, j$, there exists a unique $x \in M$ with $f_i(x) = m_i$ for every $i$. Note that no pair of indices is excluded and no cocycle condition beyond the stated pairwise one is imposed.
--
--   This is the module-theoretic sheaf axiom for the structure sheaf on a distinguished affine open cover: exactness of $0 \to M \to \prod_i M_{g_i} \to \prod_{i,j} M_{g_i g_j}$, stated abstractly for arbitrary realisations of the localisations via `IsLocalizedModule`. It is used in the verification that the maps to sections of the cotangent and tangent sheaves of a morphism of schemes are bijective over an affine open.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalizedModule.existsUnique_forall_eq_of_span_range_eq_top
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] (g : ι → R) (hg : Ideal.span (Set.range g) = ⊤)
    {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module R (Mi i)]
    (fi : ∀ i, M →ₗ[R] Mi i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (fi i)]
    {Mij : ι → ι → Type*} [∀ i j, AddCommGroup (Mij i j)] [∀ i j, Module R (Mij i j)]
    (fij : ∀ i j, M →ₗ[R] Mij i j) [∀ i j, IsLocalizedModule (Submonoid.powers (g i * g j)) (fij i j)]
    (ρ : ∀ i j, Mi i →ₗ[R] Mij i j) (ρ' : ∀ i j, Mi j →ₗ[R] Mij i j)
    (hρ : ∀ i j, (ρ i j).comp (fi i) = fij i j) (hρ' : ∀ i j, (ρ' i j).comp (fi j) = fij i j)
    (m : ∀ i, Mi i) (hm : ∀ i j, ρ i j (m i) = ρ' i j (m j)) :
    ∃! x : M, ∀ i, fi i x = m i := by sorry
