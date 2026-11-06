-- Prove2me | Theorems.Thm_Ideal_Factors_quotientResidueEquiv_mk
-- name    : Ideal.Factors.quotientResidueEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:35.055922+00:00
-- url     : https://prove2.me/theorems/63eff57f-f30c-4c49-94df-9fd2cbab5292
-- title:
--   Factors: quotient Residue Equiv mk
-- statement:
--   The Factors construction uses the quotient Residue Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralTraceResidue.lean#L69-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Direct/IntegralTraceResidue.lean#L69-L74

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

theorem Ideal.Factors.quotientResidueEquiv_mk
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsMaximal] (x : A) :
    quotientResidueEquiv I (Ideal.Quotient.mk I x) =
      algebraMap A I.ResidueField x := by sorry
