-- Prove2me | Theorems.Thm_Ideal_Factors_integralTrace_mod_eq_sum_ramificationIdx_mul
-- name    : Ideal.Factors.integralTrace_mod_eq_sum_ramificationIdx_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:56.094205+00:00
-- url     : https://prove2.me/theorems/b73e2f34-3961-4f3c-adb9-34a596ee8023
-- title:
--   Factors: integral Trace mod eq sum ramification Idx mul
-- statement:
--   Reduction of the actual direct integral trace at a height-one polynomial
--   prime is the finite ramification-weighted sum of the upper quotient traces.
--   The equality combines Mathlib's integral-trace reduction theorem with the
--   proved Dedekind quotient-factor trace decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralTraceResidue.lean#L45-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralTraceResidue.lean#L45-L58

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

theorem Ideal.Factors.integralTrace_mod_eq_sum_ramificationIdx_mul
    (p : Ideal R) [p.IsMaximal]
    (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    Ideal.Quotient.mk p (Algebra.intTrace R S x) =
      ∑ P : (factors (map (algebraMap R S) p)).toFinset,
        (ramificationIdx' p (P : Ideal S) : R ⧸ p) *
          Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
            (Ideal.Quotient.mk (P : Ideal S) x) := by sorry
