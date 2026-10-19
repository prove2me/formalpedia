-- Prove2me | Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyExactSequence_range_eq_ker
-- name    : MazurTransfer.ContinuousFirstCohomologyExactSequence.range_eq_ker
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T02:09:23.901785+00:00
-- url     : https://prove2.me/theorems/5e8cc62d-7656-4bf8-9115-99613784ff89
-- title:
--   A discrete coefficient short exact sequence is exact at the middle continuous H1
-- statement:
--   Let G be a group equipped with a topology. Let M, N and P be discrete topological commutative groups with the original G actions, continuous on N. Let i:M to N and p:N to P be equivariant group homomorphisms with i injective, p surjective, and p(n)=1 exactly when n lies in the image of i. Then the image of the induced map H1_cont(G,M) to H1_cont(G,N) equals the kernel of H1_cont(G,N) to H1_cont(G,P), for the existing continuous-cocycle presentation. Every complete original hypothesis and binder is retained. The named downstream consumer is the actual ordered norm-character H1 kernel control.
-- source:
--   Original MazurTheorem ContinuousFirstCohomologyExactSequence.range_eq_ker, Apache-2.0. Original main proof and both original proof-valued helpers retained with complete original type comparisons. The helpers are kept in the submitted proof and excluded from the public statement preamble. Original public kernel-cocycle lift and coboundary constructors are reused.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a short exact sequence of discrete coefficient groups
is exact at the middle EXISTING continuous H1. Named downstream consumer:
continuous H1 kernel control for the actual ordered norm-character sequences.
No injectivity or surjectivity of the outer H1 maps is asserted.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyKernelLiftData
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyCoboundaryData

noncomputable section
open MazurTransfer
open MazurTransfer.ContinuousFirstCohomologyPresentation
open MazurTransfer.ContinuousFirstCohomologyCoefficientMap

theorem MazurTransfer.ContinuousFirstCohomologyExactSequence.range_eq_ker (G M N P : Type) [Group G] [CommGroup M] [CommGroup N] [CommGroup P]
  [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]
  [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [IsTopologicalGroup M] [IsTopologicalGroup N] [IsTopologicalGroup P]
  [DiscreteTopology M] [DiscreteTopology N] [DiscreteTopology P] [ContinuousSMul G N]
(i : M →* N) (p : N →* P)
  (hei : ∀ (g : G) (m : M), i (g • m) = g • i m)
  (hep : ∀ (g : G) (n : N), p (g • n) = g • p n) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : ∀ n : N, p n = 1 ↔ ∃ m : M, i m = n) :
    (coefficientMap G M N i hei continuous_of_discreteTopology).range =
      (coefficientMap G N P p hep continuous_of_discreteTopology).ker := by sorry
