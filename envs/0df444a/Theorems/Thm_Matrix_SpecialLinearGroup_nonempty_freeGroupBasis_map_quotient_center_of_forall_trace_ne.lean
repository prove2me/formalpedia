-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne
-- name    : Matrix.SpecialLinearGroup.nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/8a515b68-0526-52cb-8cbc-52fbd29a8276
-- title:
--   Free image in PSL₂(ℤ) of a torsion-free congruence-type subgroup
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ (matrices over $\mathbb{Z}$ indexed by `Fin 2`) which is of finite index, i.e. carries the `FiniteIndex` instance, and assume: (i) $-1 \in \Gamma$; (ii) for every $\gamma \in \Gamma$ the trace of the underlying integral $2 \times 2$ matrix is different from $0$, from $1$ and from $-1$. The conclusion is that the type `FreeGroupBasis (Fin (1 + Γ.index / 6))` of the image of $\Gamma$ under the canonical projection $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z})/Z$, $Z$ the centre, is nonempty; that is, the image $\bar\Gamma$ of $\Gamma$ in $\mathrm{PSL}_2(\mathbb{Z})$ admits a basis as a free group indexed by the finite type with $1 + [\mathrm{SL}_2(\mathbb{Z}):\Gamma]/6$ elements, where the quotient is natural-number division. So $\bar\Gamma$ is free of rank $1 + [\mathrm{SL}_2(\mathbb{Z}):\Gamma]/6$, the index being that of $\Gamma$ in the full group; no divisibility assertion about the index is made, the division being truncated.
--
--   This is the classical statement that a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$ containing $-1$ and having no elliptic elements has free image in $\mathrm{PSL}_2(\mathbb{Z})$, of rank $1 + [\mathrm{SL}_2(\mathbb{Z}):\Gamma]/6$; it is obtained by transporting the Kurosh rank formula [`Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank`](thm.html#Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank) along the isomorphism $\mathrm{PSL}_2(\mathbb{Z}) \cong C_2 * C_3$ of [`ModularGroup.exists_mulEquiv_freeProduct_quotient_center`](thm.html#ModularGroup.exists_mulEquiv_freeProduct_quotient_center), together with the index computation [`Subgroup.card_orbitRelQuotient_mul_card_eq_index`](thm.html#Subgroup.card_orbitRelQuotient_mul_card_eq_index). It feeds the construction of explicit free generators for such subgroups and, through that, the vanishing of $H^2$ and the degree-one surjectivity statements used in the cohomological part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_SpecialLinearGroup_nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.SpecialLinearGroup.nonempty_freeGroupBasis_map_quotient_center_of_forall_trace_ne
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) :
    Nonempty (FreeGroupBasis (Fin (1 + Γ.index / 6))
      (Γ.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℤ))))) := by sorry
