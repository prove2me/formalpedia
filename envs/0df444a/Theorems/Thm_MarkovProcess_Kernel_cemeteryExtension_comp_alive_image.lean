-- Prove2me | Theorems.Thm_MarkovProcess_Kernel_cemeteryExtension_comp_alive_image
-- name    : MarkovProcess.Kernel.cemeteryExtension_comp_alive_image
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:26.840784+00:00
-- url     : https://prove2.me/theorems/4b64a5ad-b1ce-47a7-a7e1-723a25f6979b
-- title:
--   MarkovProcess: cemeteryExtension_comp_alive_image
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeteryExtension_b0b7bd17
import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeterySemigroup_149c26e5
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cemetery extensions of sub-Markov kernel semigroups

This file shows that conservative cemetery extension preserves the identity
kernel and composition of sub-Markov kernels.  Consequently, applying the
extension at every time turns any sub-Markov kernel semigroup into a
conservative semigroup on the cemetery state space.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace Kernel







end Kernel

namespace SubMarkovKernelSemigroup



variable (P : SubMarkovKernelSemigroup α)







end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.Kernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cemetery extensions of sub-Markov kernel semigroups

This file shows that conservative cemetery extension preserves the identity
kernel and composition of sub-Markov kernels.  Consequently, applying the
extension at every time turns any sub-Markov kernel semigroup into a
conservative semigroup on the cemetery state space.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal



variable {α : Type*} [MeasurableSpace α]




open MarkovProcess.Kernel in

theorem MarkovProcess.Kernel.cemeteryExtension_comp_alive_image (η κ : Kernel α α)
    (x : α) {s : Set α} (hs : MeasurableSet s) :
    cemeteryExtension (η.comp κ) (Cemetery.alive x) (Cemetery.alive '' s) =
      ((cemeteryExtension η).comp (cemeteryExtension κ))
        (Cemetery.alive x) (Cemetery.alive '' s) := by sorry
