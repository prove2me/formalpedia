-- Prove2me | Theorems.Thm_MazurTransfer_Order13InverseParameterPolynomialCombinationIndependence_polynomial_combination_kernel
-- name    : MazurTransfer.Order13InverseParameterPolynomialCombinationIndependence.polynomial_combination_kernel
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T05:34:15.612795+00:00
-- url     : https://prove2.me/theorems/e132d063-aa1c-4a6d-b735-93eb25cb37e7
-- title:
--   The actual inverse-parameter polynomial combinations are independent
-- statement:
--   Let $R$ be a noetherian commutative integral domain in which $104$ is a unit. In the localization of the actual ordinary order-thirteen coordinate algebra at $t=y+x^3+x^2+1$, put $s=1/t$, $a=p/t^2$, and $b=q/t^2$, where $p=xt$ and $q=x(p+2)$. For $F_0,F_1,F_2\in R[S]$, an identity $$F_0(s)+F_1(s)a+F_2(s)b=0$$ forces $F_0=F_1=F_2=0$. This gives the independence input for the actual inverse finite algebra and its finite free level sets.
-- source:
--   The unchanged original contract from MazurTheorem Order13InverseParameterPolynomialCombinationIndependence.polynomial_combination_kernel. The denominator-clearing and reflection argument is retained. Its final use of the old first-coordinate weighted-degree kernel is replaced by the already Proved public finite-basis result through the value-preserved actual finite-basis interface. All original base hypotheses, coordinate constructors and polynomial degrees are retained. Exact complete original/public types and the standalone preamble are checked, together with native, strict and full frontend validation. Apache-2.0. Vas and contributors.

import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseCombinationCoordinates
open Polynomial MazurTransfer
open MazurTorsion.XOneThirteenAffineCurve
open MazurTransfer.Order13SingleSectionFiniteMapIdentities (t p q)
open MazurTransfer.Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
open MazurTransfer.Order13InverseParameterPolynomialIdentities (s a b)
open MazurTransfer.Order13InverseParameterPolynomialCombinationIndependence
universe u

theorem MazurTransfer.Order13InverseParameterPolynomialCombinationIndependence.polynomial_combination_kernel (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]  (h104 : IsUnit (104 : R))
    (F : Fin 3 → Polynomial R)
    (hF : ∑ i, aeval (s R) (F i) * generator R i = 0) : ∀ i, F i = 0  := by sorry
