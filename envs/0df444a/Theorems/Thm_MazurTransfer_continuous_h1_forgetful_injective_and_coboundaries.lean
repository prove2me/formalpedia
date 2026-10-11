-- Prove2me | Theorems.Thm_MazurTransfer_continuous_h1_forgetful_injective_and_coboundaries
-- name    : MazurTransfer.continuous_h1_forgetful_injective_and_coboundaries
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T19:53:42.745192+00:00
-- url     : https://prove2.me/theorems/d7b38e36-16dd-45bf-880f-5bf100236258
-- title:
--   Continuous first cohomology embeds in algebraic first cohomology
-- statement:
--   Let G act continuously on an abelian topological group M. Continuous first cohomology, presented by continuous cocycles modulo coboundaries, has an injective forgetful homomorphism to algebraic first cohomology. A continuous cocycle represents zero exactly when it is an algebraic coboundary, and every algebraic coboundary is continuous. This identifies precisely the equivalence relation needed for continuous Kummer classes.
--
--   **Formalization Note** The interface supplies the quotient of continuous algebraic cocycles by the kernel of the algebraic cohomology class map; the theorem checks the coboundary interpretation. A comparison to Mathlib homological continuous cohomology is a separate interface.
-- source:
--   Owned MazurTheorem continuous norm descent interface, Apache-2.0; Mathlib groupCohomology.H1π_eq_zero_iff, QuotientAddGroup.kerLift_injective and continuous group actions at pin 0df444a360eaa60ab8c11dca51a86af692955474. Named downstream consumer: the actual rational Picard norm-quotient Kummer injection into continuous H1.

import Definitions.Def_mazur_continuous_h1_cocycle_quotient
open MazurTransfer.PublicContinuousFirstCohomologyPresentation

theorem MazurTransfer.continuous_h1_forgetful_injective_and_coboundaries
    (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] [ContinuousSMul G M] :
    Function.Injective (forgetH1 G M) ∧
      (∀ z : continuousCocycles G M, classMap G M z = 0 ↔
        (z.val : G → Additive M) ∈ groupCohomology.coboundaries₁ (rep G M)) ∧
      (∀ f : G → Additive M, f ∈ groupCohomology.coboundaries₁ (rep G M) →
        Continuous (fun g : G => (Additive.toMul (f g) : M))) := by sorry
