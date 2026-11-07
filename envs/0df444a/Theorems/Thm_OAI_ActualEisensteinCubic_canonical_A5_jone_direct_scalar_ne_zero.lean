-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jone_direct_scalar_ne_zero
-- name    : OAI.ActualEisensteinCubic.canonical_A5_jone_direct_scalar_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:45:40.701082+00:00
-- url     : https://prove2.me/theorems/db08d478-3b3a-4367-b627-1bda2a106023
-- title:
--   Actual Eisenstein Cubic: canonical A5 jone direct scalar ne zero
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical A5 jone direct scalar ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L95-L127
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L95-L127

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

theorem OAI.ActualEisensteinCubic.canonical_A5_jone_direct_scalar_ne_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (ε : O ⧸ P) (hε : ε ≠ 0) :
    let χ := canonicalSextic P hgood
    ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
      gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) ≠ 0 := by sorry
