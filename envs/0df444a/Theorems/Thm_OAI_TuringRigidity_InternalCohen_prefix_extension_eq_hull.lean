-- Prove2me | Theorems.Thm_OAI_TuringRigidity_InternalCohen_prefix_extension_eq_hull
-- name    : OAI.TuringRigidity.InternalCohen.prefix_extension_eq_hull
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:41:09.068498+00:00
-- url     : https://prove2.me/theorems/946554ed-b46f-476f-bdbe-5fb82e379113
-- title:
--   OAI.TuringRigidity.InternalCohen.prefix_extension_eq_hull: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.InternalCohen.prefix_extension_eq_hull` of [lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenPrefixHull.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenPrefixHull.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.InternalCohen`, with `open TransitiveNameModel BoundedSetTheory CohenBorelForcing CountableForcing`):
--
--   ```lean
--   theorem prefix_extension_eq_hull (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
--       (A : Oracle) (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A))) :
--       genericExtensionSet M conditions (pushFilter (realFilter A)).carrier =
--         RealGeneratedModel.hull M (realCode A)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` and `OAI.TuringRigidity.CountableForcing.GenericFilter` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` and `OAI.TuringRigidity.BoundedSetTheory.realCode` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenBorelForcing.realFilter` and `OAI.TuringRigidity.InternalCohen.conditions` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.InternalCohen.pushFilter` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RealGeneratedModel.hull` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.CohenDisjointPrefixPair.exists_iterated_pair`, `OAI.TuringRigidity.GroundPrefixOverwrite.overwrite_generic`, `OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair` and `OAI.TuringRigidity.RelativeConstructible.real_hull_generic_column_realizes` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenPrefixHull.lean (declaration OAI.TuringRigidity.InternalCohen.prefix_extension_eq_hull)

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

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem prefix_extension_eq_hull (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A))) :
    genericExtensionSet M conditions (pushFilter (realFilter A)).carrier =
      RealGeneratedModel.hull M (realCode A) := by
  sorry

end TuringRigidity.InternalCohen

end OAI
end
