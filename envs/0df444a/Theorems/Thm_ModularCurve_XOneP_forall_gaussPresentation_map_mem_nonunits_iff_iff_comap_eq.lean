-- Prove2me | Theorems.Thm_ModularCurve_XOneP_forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq
-- name    : ModularCurve.XOneP.forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/d480c155-0690-5264-844b-23d8b59229f1
-- title:
--   Pull-back of V equals the Gauss ring iff non-units match
-- statement:
--   Let $A$ be a commutative local ring with residue map $\mathrm{residue}\colon A \to A/\mathfrak m_A$, let $L$ be a field which is an $A$-algebra, and let $K$ be an intermediate field of the Laurent series field $\mathrm{LaurentSeries}\,L$ over $L$. Let $W_0, W_1$ be valuation subrings of $K$, in arbitrary relative position. Assume two properties of $W_0$ relative to $A$-integral presentations: (h4) an element $f \in K$ lies in $W_0$ if and only if there are power series $x, y \in A[[T]]$ with $y$ having nonzero image under the coefficientwise residue map, such that, inside $\mathrm{LaurentSeries}\,L$, $f \cdot \widehat{y} = \widehat{x}$, where $\widehat{\;\cdot\;}$ denotes the image of a power series over $A$ under the coefficientwise map to $L$ followed by the inclusion of $L[[T]]$ into Laurent series; (h6) for every $f \in K$ and every such pair $(x,y)$ with $\bar y \neq 0$ and $f\cdot\widehat y = \widehat x$, the element $f$ is a non-unit of $W_0$ if and only if $\bar x = 0$. Let further $K'$ be a field, $\iota\colon K \to K'$ a ring homomorphism, and $V$ a valuation subring of $K'$ whose pull-back $\iota^{-1}V$ equals $W_0$ or $W_1$. The conclusion is an equivalence: the condition that for all $f \in K$ and all $x, y \in A[[T]]$ with $\bar y \neq 0$ and $f \cdot \widehat y = \widehat x$ one has $\iota f \in V.\mathrm{nonunits}$ (the non-units of $V$ in $K'$, i.e. those $z$ with $z = 0$ or $z^{-1} \notin V$) if and only if $\bar x = 0$, holds precisely when $\iota^{-1} V = W_0$.
--
--   The hypotheses (h4), (h6) describe $W_0$ as the Gauss valuation ring on $K$, with its maximal ideal read off from the reduction of the numerator of an $A$-integral presentation; the statement says that a valuation subring upstairs, known a priori to pull back to one of the two rings $W_0$, $W_1$, pulls back to the Gauss ring exactly when its non-units are detected by the vanishing of those reduced numerators. It is used in the analysis of the two legs over the Gauss centre in the Hecke correspondence on $X_1$, by [`ModularCurve.XOneP.forall_valuationSubring_heckeRoof_gaussCentre_alpha_iff_beta_x1_mul`](thm.html#ModularCurve.XOneP.forall_valuationSubring_heckeRoof_gaussCentre_alpha_iff_beta_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.XOneP.forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq
    (A : Type*) [CommRing A] [IsLocalRing A] (L : Type*) [Field L] [Algebra A L]
    (K : IntermediateField L (LaurentSeries L))
    (W₀ W₁ : ValuationSubring ↥K)
    (h4 : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (h6 : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (K' : Type*) [Field K'] (ι : ↥K →+* K') (V : ValuationSubring K')
    (hV : V.comap ι = W₀ ∨ V.comap ι = W₁) :
    (∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (ι f ∈ V.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) ↔
      V.comap ι = W₀ := by sorry
