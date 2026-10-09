-- Prove2me | Theorems.Thm_MazurProof_N13ContractQuotientXYBasis_exists_contractQuotient_basis_oneX_or_oneY
-- name    : MazurProof.N13ContractQuotientXYBasis.exists_contractQuotient_basis_oneX_or_oneY
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:26:49.743084+00:00
-- url     : https://prove2.me/theorems/e816701e-6936-4b0d-959f-8c5ed20f93ee
-- title:
--   Mazur 13 port: exists_contractQuotient_basis_oneX_or_oneY
-- statement:
--   Supporting lemma `exists_contractQuotient_basis_oneX_or_oneY` (namespace `MazurProof.N13ContractQuotientXYBasis`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13ContractQuotientXYBasis.lean#L106

import Mathlib
import Definitions.Def_MazurN13_L2

open MazurProof MazurProof.N13ContractQuotientXYBasis
open Module
open Polynomial
open scoped TensorProduct
universe uF uK uA uι
attribute [local instance] MazurProof.N13ContractQuotientXYBasis.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13ContractQuotientXYBasis.baseSpecialAlgebra

theorem MazurProof.N13ContractQuotientXYBasis.exists_contractQuotient_basis_oneX_or_oneY (D : SexticMumford.SemiMumford Model) (hdeg : D.u.natDegree = 2) (hfinite : Module.Finite R₂ (IntegralRing ⧸ N13IntegralModelContraction.contractIdeal (N13CanonicalContractionQuotient.graphIdeal D))) : (∃ b : Basis (Fin 2) R₂ (IntegralRing ⧸ N13IntegralModelContraction.contractIdeal (N13CanonicalContractionQuotient.graphIdeal D)), (b : Fin 2 → IntegralRing ⧸ N13IntegralModelContraction.contractIdeal (N13CanonicalContractionQuotient.graphIdeal D)) = N13FiniteFlatBasisLift.oneX (Ideal.Quotient.mk (N13IntegralModelContraction.contractIdeal (N13CanonicalContractionQuotient.graphIdeal D)) N13CanonicalContractionQuotient.integralX)) ∨ (∃ b : Basis (Fin 2) R₂ (IntegralRing ⧸ N13IntegralModelContraction.contractIdeal (N13CanonicalContractionQuotient.graphIdeal D)), (b : Fin 2 → IntegralRing ⧸ N13IntegralModelContraction.contractIdeal (N13CanonicalContractionQuotient.graphIdeal D)) = N13FiniteFlatBasisLift.oneX (Ideal.Quotient.mk (N13IntegralModelContraction.contractIdeal (N13CanonicalContractionQuotient.graphIdeal D)) integralY)) := by sorry
