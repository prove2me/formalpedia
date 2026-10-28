-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_existsUnique_continuousProcess_of_hasKolmogorovMoments
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:31:52.90045+00:00
-- url     : https://prove2.me/theorems/bb98c4b4-5e87-47e7-bee6-76e65d1d55ce
-- title:
--   Existence and uniqueness of the continuous-path Markov process of a Feller semigroup
-- statement:
--   For a nonempty locally compact Polish state space, a conservative Feller sub-Markov kernel semigroup satisfying the intrinsic Kolmogorov moment condition gives rise to a unique Markov kernel into continuous paths. Every finite-dimensional path distribution is the corresponding finite-set transition kernel of the semigroup. This is the main theorem of Scott Armstrong's Lean 4 MarkovProcess formalisation. The faithful statement is staged while its supporting definitions and theorem imports are migrated; it must not be submitted until the missing dependencies are published and checked by Prove2Me's remote compiler.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Main.lean#L385-L398

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_MainSupport

open MeasureTheory ProbabilityTheory MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped NNReal

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
    {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
    [Nonempty alpha] [LocallyCompactSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I := by sorry
