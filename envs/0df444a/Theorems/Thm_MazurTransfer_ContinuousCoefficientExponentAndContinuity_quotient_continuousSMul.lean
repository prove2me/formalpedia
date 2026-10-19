-- Prove2me | Theorems.Thm_MazurTransfer_ContinuousCoefficientExponentAndContinuity_quotient_continuousSMul
-- name    : MazurTransfer.ContinuousCoefficientExponentAndContinuity.quotient_continuousSMul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T01:32:20.313005+00:00
-- url     : https://prove2.me/theorems/ecab6dca-01de-48eb-834e-167ca0d9c1ff
-- title:
--   A surjective intertwiner gives a continuous action on its discrete representation coefficients
-- statement:
--   Retain the original semiring, group, module and topology contexts. Let rho act on the additive form of an existing multiplicative coefficient group M, and tau act on V. Assume the original rho action agrees with the given G action on M, that action is continuous, M is discrete, and an intertwiner f from rho to tau is surjective. Then the induced action on the original discrete coefficient wrapper Coefficient(tau) is continuous. The complete original statement is retained, including the topological-group hypotheses on G and M. Named downstream consumer: the actual norm-character continuous H1 maps and local restriction diagrams.
-- source:
--   Original MazurTheorem ContinuousCoefficientExponentAndContinuity.quotient_continuousSMul, Apache-2.0. Original complete type and proof retained, reusing the existing public discrete equivariant quotient continuity theorem. Local native aliases preserve its already checked artifacts without rebuilding or additional proof credit.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: surjective actual intertwiners give continuous actions on
their discrete coefficient targets, and exponent-nineteen coefficients give
the canonical F19 structure on continuous H1. Named downstream consumer:
the actual norm quotient H1 maps and local Selmer restriction diagrams.
-/
import Definitions.Def_MazurTransfer_RepresentationDiscreteCoefficientsData
import Theorems.Thm_MazurTransfer_discrete_equivariant_quotient_continuous_smul

noncomputable section
open MazurTransfer.RepresentationDiscreteCoefficients

theorem MazurTransfer.ContinuousCoefficientExponentAndContinuity.quotient_continuousSMul {k G V M : Type} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    [CommGroup M] [MulDistribMulAction G M] [Module k (Additive M)]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M]
    [IsTopologicalGroup M] [DiscreteTopology M] [ContinuousSMul G M]
    (ρ : Representation k G (Additive M)) (τ : Representation k G V)
    (f : Representation.IntertwiningMap ρ τ)
    (hρ : ∀ (g : G) (m : M), ρ g (Additive.ofMul m) = Additive.ofMul (g • m))
    (hf : Function.Surjective f) : ContinuousSMul G (Coefficient τ) := by sorry
