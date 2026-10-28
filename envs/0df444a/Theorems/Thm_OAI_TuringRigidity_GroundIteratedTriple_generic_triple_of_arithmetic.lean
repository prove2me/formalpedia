-- Prove2me | Theorems.Thm_OAI_TuringRigidity_GroundIteratedTriple_generic_triple_of_arithmetic
-- name    : OAI.TuringRigidity.GroundIteratedTriple.generic_triple_of_arithmetic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:39:24.393078+00:00
-- url     : https://prove2.me/theorems/d41fdbe1-581c-4162-96f4-d1904abf03e2
-- title:
--   OAI.TuringRigidity.GroundIteratedTriple.generic_triple_of_arithmetic: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.GroundIteratedTriple.generic_triple_of_arithmetic` of [lean/OAI/Computability/DegreeRigidity/Representation/GroundIteratedTriple.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/GroundIteratedTriple.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.GroundIteratedTriple`, with `open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing`, `open InternalCohen CohenBorelForcing UniformArithmetic`):
--
--   ```lean
--   theorem generic_triple_of_arithmetic (M : ZFSet.{0})
--       (O : Oracles) (hO : ∀ i, realCode (O i) ∈ M)
--       (Y L R : Oracle) (hY : ArithmeticPrefixForcing.Generic O Y)
--       (hN : RealGeneratedModel.Contains M (realCode Y) (RealGeneratedModel.hull M (realCode Y)))
--       (hL : GroundGeneric (RealGeneratedModel.hull M (realCode Y)) (pushFilter (realFilter L)))
--       (hR : GroundGeneric (genericExtensionSet (RealGeneratedModel.hull M (realCode Y)) conditions
--         (pushFilter (realFilter L)).carrier) (pushFilter (realFilter R))) :
--       ArithmeticPrefixForcing.Generic O (join Y (join L R))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.join`, `OAI.TuringRigidity.ArithmeticPrefixForcing.Generic`, `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.UniformArithmetic.Oracles`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` and `OAI.TuringRigidity.CountableForcing.GenericFilter` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.realCode` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenBorelForcing.realFilter` and `OAI.TuringRigidity.InternalCohen.conditions` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.InternalCohen.pushFilter` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RealGeneratedModel.Contains` and `OAI.TuringRigidity.RealGeneratedModel.hull` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.RealHullGenericTriple.exists_generic_prefix_triple` and `OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/GroundIteratedTriple.lean (declaration OAI.TuringRigidity.GroundIteratedTriple.generic_triple_of_arithmetic)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A006
import Definitions.Def_OAIQ064A007

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GroundIteratedTriple
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open InternalCohen CohenBorelForcing UniformArithmetic
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem generic_triple_of_arithmetic (M : ZFSet.{0})
    (O : Oracles) (hO : ∀ i, realCode (O i) ∈ M)
    (Y L R : Oracle) (hY : ArithmeticPrefixForcing.Generic O Y)
    (hN : RealGeneratedModel.Contains M (realCode Y) (RealGeneratedModel.hull M (realCode Y)))
    (hL : GroundGeneric (RealGeneratedModel.hull M (realCode Y)) (pushFilter (realFilter L)))
    (hR : GroundGeneric (genericExtensionSet (RealGeneratedModel.hull M (realCode Y)) conditions
      (pushFilter (realFilter L)).carrier) (pushFilter (realFilter R))) :
    ArithmeticPrefixForcing.Generic O (join Y (join L R)) := by
  sorry

end TuringRigidity.GroundIteratedTriple

end OAI
end
