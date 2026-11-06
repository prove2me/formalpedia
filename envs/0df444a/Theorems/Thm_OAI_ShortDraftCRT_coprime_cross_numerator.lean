-- Prove2me | Theorems.Thm_OAI_ShortDraftCRT_coprime_cross_numerator
-- name    : OAI.ShortDraftCRT.coprime_cross_numerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:16:51.156614+00:00
-- url     : https://prove2.me/theorems/3d16dad5-fca6-43d3-914e-f55b6dafa2fe
-- title:
--   Short Draft CRT: coprime cross numerator
-- statement:
--   The Short Draft CRT construction uses the coprime cross numerator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L76-L89
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ChineseRemainder/AdditiveCharacters.lean#L76-L89

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftCRT
open AddChar
variable {K : Type*} [Field K]

theorem OAI.ShortDraftCRT.coprime_cross_numerator
    {R : Type*} [CommRing R] (a c₀ h r : R)
    (hfixed : IsCoprime a c₀)
    (hmoving : IsCoprime h r)
    (hmod : IsCoprime c₀ r) :
    IsCoprime (a * r + h * c₀) (c₀ * r) := by sorry
