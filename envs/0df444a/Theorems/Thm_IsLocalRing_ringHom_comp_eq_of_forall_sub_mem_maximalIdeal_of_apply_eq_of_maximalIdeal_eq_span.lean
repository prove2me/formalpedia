-- Prove2me | Theorems.Thm_IsLocalRing_ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span
-- name    : IsLocalRing.ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/50c28caf-682b-5182-949b-517508946a4c
-- title:
--   Residually trivial endomorphism fixing κ(varpi) fixes κ
-- statement:
--   Let $W$ be a commutative ring which is a domain and a discrete valuation ring, complete and separated for the adic topology of its maximal ideal $\mathfrak m_W$, and let $\varpi \in W$ be an element with $\mathfrak m_W = (\varpi)$. Let $R$ be a commutative local ring, complete and separated for the adic topology of its maximal ideal $\mathfrak m_R$, whose residue field $R/\mathfrak m_R$ is finite, and let $\kappa : W \to R$ be a ring homomorphism which is local, i.e. carries non-units to non-units. Let $\theta : R \to R$ be a ring endomorphism such that $\theta(r) - r \in \mathfrak m_R$ for every $r \in R$, and such that $\theta(\kappa(\varpi)) = \kappa(\varpi)$. Then the composite of $\kappa$ with $\theta$ equals $\kappa$, that is, $\theta(\kappa(w)) = \kappa(w)$ for all $w \in W$, as an equality of ring homomorphisms $W \to R$. No assumption is made that $\varpi$ is non-zero or that $R$ is a domain, nor that $\theta$ is injective or surjective.
--
--   This is a rigidity statement for a complete discrete valuation coefficient ring inside a complete local ring with finite residue field: an endomorphism of $R$ that is trivial on the residue field and fixes the image of the uniformiser fixes all of $\kappa(W)$. It is used in the normalisation of local charts, in [`DrinfeldCurve.LocalChart.exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal`](thm.html#DrinfeldCurve.LocalChart.exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal), where the coefficient homomorphism must be shown to be untouched by a change of coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : maximalIdeal W = Ideal.span {ϖ})
    (R : Type) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Finite (ResidueField R)]
    (κ : W →+* R) [IsLocalHom κ]
    (θ : R →+* R) (hres : ∀ r : R, θ r - r ∈ maximalIdeal R) (hfix : θ (κ ϖ) = κ ϖ) :
    θ.comp κ = κ := by sorry
