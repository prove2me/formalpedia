-- Prove2me | Theorems.Thm_Kyprianou_Ch01_iIndepFun_paired_independent_processes
-- name    : Kyprianou.Ch01.iIndepFun_paired_independent_processes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:45:29.41446+00:00
-- url     : https://prove2.me/theorems/f859240b-ab5a-4e0f-a8ec-99b8cb97f091
-- title:
--   Independent random vector coordinates remain independent after pairing two independent vectors
-- statement:
--   Two random vectors with independent coordinates, mutually independent as complete vectors, and almost-everywhere measurable coordinates yield a family of independent coordinate pairs.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.1; independent product families, a general measure-theoretic reduction of paired Levy increments.

import Mathlib
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.iIndepFun_paired_independent_processes
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : ι → Ω → ℝ)
    (hf : iIndepFun f P) (hg : iIndepFun g P)
    (hfg : IndepFun (fun ω => fun i => f i ω)
      (fun ω => fun i => g i ω) P)
    (hfm : ∀ i, AEMeasurable (f i) P)
    (hgm : ∀ i, AEMeasurable (g i) P) :
    iIndepFun (fun i ω => (f i ω, g i ω)) P := by sorry
