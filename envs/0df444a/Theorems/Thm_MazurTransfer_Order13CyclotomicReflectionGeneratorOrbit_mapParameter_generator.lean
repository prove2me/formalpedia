-- Prove2me | Theorems.Thm_MazurTransfer_Order13CyclotomicReflectionGeneratorOrbit_mapParameter_generator
-- name    : MazurTransfer.Order13CyclotomicReflectionGeneratorOrbit.mapParameter_generator
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T22:35:37.600923+00:00
-- url     : https://prove2.me/theorems/8d9a3cea-8648-4738-921d-bf4e1e51a4f3
-- title:
--   Cyclotomic coefficient doubling sends the reflection parameter to its fifth diamond iterate
-- statement:
--   Let $K$ be a field of characteristic zero, let $z$ be a primitive thirteenth root of unity, and let $\sigma$ be a field automorphism with $\sigma(z)=z^2$. For the original cyclotomic reflection parameter $a(z)$ and the original diamond parameter transformation $D$,
--   \[\sigma(a(z))=D^5(a(z)).\]
--   The fifth iterate is displayed literally in the formal statement; its full type agrees with the original named-iterate formulation.
-- source:
--   MazurTheorem Order13CyclotomicReflectionGeneratorOrbit.mapParameter_generator, with eighteen exact original helper types and three exact whole helper values; the original fifthParameter value is expanded in the public statement and checked definitionally against the complete original statement; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13CyclotomicReflectionParameterOriginalPolynomialDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13ReflectionDiamondParameterOriginalDataAndConstructorCertificatesMinimalPublicNamespaceV220261018
import Definitions.Def_MazurTransfer_Order13ActualCoefficientFunctionFieldActionAndReflectionParameterOriginalDataMinimalPublicNamespacesV220261018
noncomputable section
universe u
open MazurTransfer.Order13CyclotomicReflectionCoefficients MazurTransfer.Order13ReflectionParameter
open MazurTransfer.Order13ReflectionParameterArithmetic MazurTransfer.Order13ReflectionSexticSymmetry
open MazurTransfer.Order13DiamondSexticSymmetry MazurTransfer.Order13ActualReflectionCoefficientCovariance

theorem MazurTransfer.Order13CyclotomicReflectionGeneratorOrbit.mapParameter_generator {K : Type u} [Field K] [CharZero K] (σ : K ≃+* K) {z : K} (hz : IsPrimitiveRoot z 13)
    (hσ : σ z = z ^ 2) :
    mapParameter K σ (cyclotomicParameter z hz) = diamondParameter (diamondParameter (diamondParameter (diamondParameter (diamondParameter (cyclotomicParameter z hz))))) := by sorry
