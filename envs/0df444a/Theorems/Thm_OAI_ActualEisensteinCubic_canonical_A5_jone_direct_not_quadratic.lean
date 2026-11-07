-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonical_A5_jone_direct_not_quadratic
-- name    : OAI.ActualEisensteinCubic.canonical_A5_jone_direct_not_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:45:48.977109+00:00
-- url     : https://prove2.me/theorems/0a138172-5b04-46a8-81ff-00571bc5e6bb
-- title:
--   Actual Eisenstein Cubic: canonical A5 jone direct not quadratic
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical A5 jone direct not quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L84-L93
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LocalNonvanishing.lean#L84-L93

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

theorem OAI.ActualEisensteinCubic.canonical_A5_jone_direct_not_quadratic (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    canonicalSextic P hgood ≠ (canonicalSextic P hgood) ^ 3 := by sorry
