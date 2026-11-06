-- Prove2me | Theorems.Thm_Ideal_Factors_trace_quotient_map_eq_sum_ramificationIdx_mul
-- name    : Ideal.Factors.trace_quotient_map_eq_sum_ramificationIdx_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:53.833389+00:00
-- url     : https://prove2.me/theorems/29b7d067-6b88-4e55-82fb-1d4517f6253f
-- title:
--   Factors: trace quotient map eq sum ramification Idx mul
-- statement:
--   The multiplication trace on the quotient by a mapped maximal ideal is
--   the sum, over its actual prime factors, of ramification-index-weighted
--   residue-field multiplication traces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/DedekindQuotientTrace.lean#L54-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Trace/DedekindQuotientTrace.lean#L54-L85

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PrimePowerQuotientTrace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_DedekindQuotientTrace
set_option autoImplicit false
open Ideal
universe u v w w'
variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
attribute [-instance] Ideal.Quotient.commSemiring
attribute [local instance]
  Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
open Ideal.Factors
open UniqueFactorizationMonoid
variable [IsDedekindDomain S] [Module.Finite R S]

theorem Ideal.Factors.trace_quotient_map_eq_sum_ramificationIdx_mul
    (p : Ideal R) [p.IsMaximal]
    (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ map (algebraMap R S) p)
        (Ideal.Quotient.mk _ x) =
      ∑ P : (factors (map (algebraMap R S) p)).toFinset,
        (ramificationIdx' p (P : Ideal S) : R ⧸ p) *
          Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
            (Ideal.Quotient.mk _ x) := by sorry
