-- Prove2me | Theorems.Thm_OAI_IdealGaussCRT_gauss_transform_crt
-- name    : OAI.IdealGaussCRT.gauss_transform_crt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:19:21.104489+00:00
-- url     : https://prove2.me/theorems/3155c802-c750-4f7d-95ae-dfaf068055be
-- title:
--   Ideal Gauss CRT: gauss transform crt
-- statement:
--   The Ideal Gauss CRT construction uses the gauss transform crt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L398-L426
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/LatticeCount.lean#L398-L426

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
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
open OAI.IdealGaussCRT
open AddChar MulChar

theorem OAI.IdealGaussCRT.gauss_transform_crt {T R S : Type*}
    [CommRing T] [Field R] [Field S]
    [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S)
    (χR : MulChar R ℂ) (χS : MulChar S ℂ)
    (ψ : AddChar T ℂ) (hχR : χR ≠ 1) (hχS : χS ≠ 1)
    (h : T) :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ (h * x)) =
      (if (e h).1 = 0 then 0 else
        (χR (e h).1)⁻¹ * gaussSum χR (leftAddChar e ψ)) *
      (if (e h).2 = 0 then 0 else
        (χS (e h).2)⁻¹ * gaussSum χS (rightAddChar e ψ)) := by sorry
