-- Prove2me | Theorems.Thm_InformationTheory_klDiv_map_measurableEquiv
-- name    : InformationTheory.klDiv_map_measurableEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:42.945088+00:00
-- url     : https://prove2.me/theorems/b522e5d3-063b-4f6c-bcfe-8f9d1518f435
-- title:
--   Information Theory: kl Div map measurable Equiv
-- statement:
--   Kullback-Leibler divergence is invariant under a measurable equivalence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/KernelCompositionKullbackLeibler.lean#L51-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ChannelCapacity/KernelCompositionKullbackLeibler.lean#L51-L66

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open InformationTheory
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem InformationTheory.klDiv_map_measurableEquiv (e : α ≃ᵐ β) (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by sorry
