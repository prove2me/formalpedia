-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlgInf_mul_chartAlgInf_laurentBaseChange_of_charZero_of_not_dvd
-- name    : ModularCurve.IgusaScheme.exists_algEquiv_tensor_chartAlgInf_mul_chartAlgInf_laurentBaseChange_of_charZero_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/9ca3373b-e294-5488-bc66-3b03399d07b2
-- title:
--   Pole chart of the X₀(Np) model base-changes to a DVR
-- statement:
--   Let $N$ be a nonzero natural number and $p$ a prime with $p \nmid N$, and write $\mathbb{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $L$ be a field of characteristic zero and let $K'$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained as `laurentBaseChange`, i.e. the subfield generated over $L$ by the coefficientwise image, under the map `coeffEmb` induced by $\mathbb{Q} \to L$, of $\mathbb{Q}$-adjoin of the integral-form ratios for $\Gamma_0(Np)$ (`qExpFunctionFieldC ℚ (Gamma0 (N*p))`). Let $A$ be a discrete valuation domain with $L$ as its fraction field, equipped with a $\mathbb{Z}_{(p)}$-algebra structure compatible with $\mathbb{Z}_{(p)} \to L$, such that the image of $p$ lies in the maximal ideal of $A$, and let $A$ act on $K'$ compatibly through $L$. Let $j' \in K'$ be nonzero with image in $\mathrm{LaurentSeries}\,L$ equal to `coeffEmb L jq`, the coefficientwise image of the $q$-expansion $q^{-1}\cdot(\text{integral power series})$ of the modular invariant. Then there is an isomorphism of $A$-algebras $e$ from $A \otimes_{\mathbb{Z}_{(p)}} \mathrm{chartAlgInf}(Np, p)$, the elements of the field $\mathrm{modularFunctionFieldFull}(Np) \subseteq \mathrm{LaurentSeries}\,\mathbb{Q}$ integral over $\mathbb{Z}_{(p)}[\,j^{-1}]$, onto `TwoChartIntegralModel.chartAlgInf A K' j'`, the elements of $K'$ integral over $A[\,j'^{-1}]$, which is compatible with $q$-expansions: for every $b$ in $\mathrm{chartAlgInf}(Np, p)$, the element $e(1 \otimes b)$, viewed in $K' \subseteq \mathrm{LaurentSeries}\,L$, equals the image of the Laurent series $b$ under `coeffEmb L`.
--
--   This identifies the chart at infinity (the pole chart in $1/j$) of the two-chart integral model of $X_0(Np)$ over a discrete valuation ring $A$ of mixed characteristic $p$ as the base change along $\mathbb{Z}_{(p)} \to A$ of the corresponding chart of the Igusa-type model over $\mathbb{Z}_{(p)}$, with the identification normalised by $q$-expansions; it is the companion of the statement for the finite chart. It is used in the analysis of which functions on the cuspidal chart fail to be integral, where the two minimal primes above $p$ in the pole chart are transported to the model over $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlgInf_mul_chartAlgInf_laurentBaseChange_of_charZero_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open AlgebraicCurve
open ModularCurve
open ModularCurve.IgusaScheme

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_algEquiv_tensor_chartAlgInf_mul_chartAlgInf_laurentBaseChange_of_charZero_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (L : Type) [Field L] [CharZero L]
    (K' : IntermediateField L (LaurentSeries L))
    (hK' : K' = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (N * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j' : ↥K') (hj' : ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j' ≠ 0)] :
    ∃ e : A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgInf (N * p) p) ≃ₐ[A]
        ↥(TwoChartIntegralModel.chartAlgInf A ↥K' j'),
      ∀ b : ↥(chartAlgInf (N * p) p),
        (((e (1 ⊗ₜ b) : ↥(TwoChartIntegralModel.chartAlgInf A ↥K' j')) : ↥K') : LaurentSeries L) =
          ModularCurve.coeffEmb L (((b : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ)) := by sorry
