-- Prove2me | Theorems.Thm_OAI_BassTrace_RightProjective_bassTraceModules_vanishing_and_support
-- name    : OAI.BassTrace.RightProjective.bassTraceModules_vanishing_and_support
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:23.013972+00:00
-- url     : https://prove2.me/theorems/a60b0321-e019-4292-8702-da9ba4524698
-- statement:
--   The theorem states that for every group G and every element x of the Grothendieck group of finitely generated projective right modules over the complex group algebra ℂ[G], the Hattori–Stallings trace of x vanishes on every conjugacy class represented by an element of infinite order. Here the Grothendieck group identifies isomorphic modules and imposes [P ⊕ Q] = [P] + [Q]. To compute the trace of a module class, realize the module as a direct summand of a finite free module, take the matrix trace of the resulting idempotent, and sum its group-algebra coefficients within each conjugacy class; this extends additively to x. The conclusion also explicitly asserts that the support of this finitely supported complex-valued function on conjugacy classes is contained in the set of classes having a finite-order representative.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BassTrace.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BassTrace.lean; bytes 22499..22829
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.Tactic
import Definitions.Def_BassTrace

namespace OAI

noncomputable section

namespace BassTrace

open scoped Classical

namespace RightProjective

open scoped Classical BigOperators

open MulOpposite

open scoped Classical

universe u v

attribute [instance] Object.addCommGroup Object.module Object.finite Object.projective

variable {R : Type u} [Ring R]

variable {G : Type u} [_root_.Group G]

theorem bassTraceModules_vanishing_and_support {G : Type u} [_root_.Group G]
    (x : ModuleK0.{u,v} (MonoidAlgebra ℂ G)) :
    (∀ g : G, ¬IsOfFinOrder g → HattoriStallings x (ConjClasses.mk g) = 0) ∧
      ↑(HattoriStallings x).support ⊆
        {c | ∃ g : G, IsOfFinOrder g ∧ ConjClasses.mk g = c} :=
  by sorry

end RightProjective
end BassTrace
end
end OAI
