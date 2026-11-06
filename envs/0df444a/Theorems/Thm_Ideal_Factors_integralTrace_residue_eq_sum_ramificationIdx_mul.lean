-- Prove2me | Theorems.Thm_Ideal_Factors_integralTrace_residue_eq_sum_ramificationIdx_mul
-- name    : Ideal.Factors.integralTrace_residue_eq_sum_ramificationIdx_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:44.875937+00:00
-- url     : https://prove2.me/theorems/2b7d711a-a217-40c8-a1c8-021310c42de1
-- title:
--   Factors: integral Trace residue eq sum ramification Idx mul
-- statement:
--   Reduction of an integral trace in the actual base residue field is the
--   finite ramification-weighted sum of the actual upper residue-field traces.
--   This transports the quotient-factor identity through the canonical quotient
--   to residue-field equivalences; it does not enumerate either residue field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralTraceResidue.lean#L144-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralTraceResidue.lean#L144-L154

import Mathlib.RingTheory.Trace.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_DedekindQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralTraceResidue
set_option autoImplicit false
open Ideal
open scoped nonZeroDivisors
open UniqueFactorizationMonoid
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
open Ideal.Factors
universe u v
variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {S : Type v} [CommRing S] [IsDedekindDomain S] [Algebra R S]
variable [Module.IsTorsionFree R S] [Module.Finite R S]

theorem Ideal.Factors.integralTrace_residue_eq_sum_ramificationIdx_mul
    (p : Ideal R) [p.IsMaximal]
    (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    algebraMap R p.ResidueField (Algebra.intTrace R S x) =
      ∑ P : (factors (map (algebraMap R S) p)).toFinset,
        (ramificationIdx' p (P : Ideal S) : p.ResidueField) *
          factorResidueTrace p P x := by sorry
