-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_cubicGauss_normalized_cube_eis
-- name    : OAI.ActualEisensteinCubic.cubicGauss_normalized_cube_eis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:37:32.641418+00:00
-- url     : https://prove2.me/theorems/1988df33-ed2b-41fb-acd4-d8c24a98e0a0
-- title:
--   Actual Eisenstein Cubic: cubic Gauss normalized cube eis
-- statement:
--   The Actual Eisenstein Cubic construction uses the cubic Gauss normalized cube eis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L361-L388
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinEmbedding.lean#L361-L388

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
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
open OAI.ActualEisensteinCubic

theorem OAI.ActualEisensteinCubic.cubicGauss_normalized_cube_eis (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    (gaussSum ((cubicChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ψ /
      (‖ConcreteTraceCRT.eisEmbedding p‖ : ℂ)) ^ 3 =
      -(ConcreteTraceCRT.eisEmbedding p) /
        (‖ConcreteTraceCRT.eisEmbedding p‖ : ℂ) := by sorry
