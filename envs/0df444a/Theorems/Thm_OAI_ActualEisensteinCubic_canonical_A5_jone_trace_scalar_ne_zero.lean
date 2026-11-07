-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jone_trace_scalar_ne_zero
-- name    : OAI.ActualEisensteinCubic.canonical_A5_jone_trace_scalar_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:46:04.877204+00:00
-- url     : https://prove2.me/theorems/8094e1d8-f45b-41f0-a8e3-0c4a4f7fc926
-- title:
--   Actual Eisenstein Cubic: canonical A5 jone trace scalar ne zero
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical A5 jone trace scalar ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L129-L144
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L129-L144

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open OAI.ActualEisensteinCubic
open AddChar MulChar

theorem OAI.ActualEisensteinCubic.canonical_A5_jone_trace_scalar_ne_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (ε : O ⧸ P) (hε : ε ≠ 0) :
    let χ := canonicalSextic P hgood
    let ψ : AddChar (O ⧸ P) ℂ := hP.symm ▸
      ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp
    ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
      gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) ≠ 0 := by sorry
