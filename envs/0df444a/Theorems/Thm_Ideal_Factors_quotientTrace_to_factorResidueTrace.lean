-- Prove2me | Theorems.Thm_Ideal_Factors_quotientTrace_to_factorResidueTrace
-- name    : Ideal.Factors.quotientTrace_to_factorResidueTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:29:46.555307+00:00
-- url     : https://prove2.me/theorems/d0c83ae5-30dc-4ebe-97d1-d6b03f993666
-- title:
--   Factors: quotient Trace to factor Residue Trace
-- statement:
--   Transporting multiplication trace on an upper ideal quotient to the base
--   residue field gives the corresponding factor residue trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralTraceResidue.lean#L93-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralTraceResidue.lean#L93-L138

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
omit [IsDedekindDomain R] [Module.IsTorsionFree R S] [Module.Finite R S]

theorem Ideal.Factors.quotientTrace_to_factorResidueTrace
    (p : Ideal R) [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) (x : S) :
    quotientResidueEquiv p
        (Algebra.trace (R ⧸ p) (S ⧸ (P : Ideal S))
          (Ideal.Quotient.mk (P : Ideal S) x)) =
      factorResidueTrace p P x := by sorry
