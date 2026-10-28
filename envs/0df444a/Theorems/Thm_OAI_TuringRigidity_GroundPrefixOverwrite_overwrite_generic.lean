-- Prove2me | Theorems.Thm_OAI_TuringRigidity_GroundPrefixOverwrite_overwrite_generic
-- name    : OAI.TuringRigidity.GroundPrefixOverwrite.overwrite_generic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:40:53.657693+00:00
-- url     : https://prove2.me/theorems/43cd7bf1-5a4c-4c8a-8851-b50b79a2ae91
-- title:
--   OAI.TuringRigidity.GroundPrefixOverwrite.overwrite_generic: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.GroundPrefixOverwrite.overwrite_generic` of [lean/OAI/Computability/DegreeRigidity/Representation/GroundPrefixOverwrite.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/GroundPrefixOverwrite.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.GroundPrefixOverwrite`, with `open TransitiveNameModel BoundedSetTheory CountableForcing CohenColumnRealName`, `open FiniteOverwrite`):
--
--   ```lean
--   theorem overwrite_generic (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
--       (A : Oracle) (hA : AtomicForcing.GroundGeneric M
--         (InternalCohen.pushFilter (CohenBorelForcing.realFilter A))) (s : List Bool) :
--       AtomicForcing.GroundGeneric M
--         (InternalCohen.pushFilter (CohenBorelForcing.realFilter (overwrite s A)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.TransitiveNameModel.Transitive` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenBorelForcing.realFilter`, `OAI.TuringRigidity.FiniteOverwrite.overwrite` and `OAI.TuringRigidity.InternalCohen.conditions` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.InternalCohen.pushFilter` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.RealHullGenericTriple.exists_prefix_real` and `OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/GroundPrefixOverwrite.lean (declaration OAI.TuringRigidity.GroundPrefixOverwrite.overwrite_generic)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A006

section

attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GroundPrefixOverwrite
open TransitiveNameModel BoundedSetTheory CountableForcing CohenColumnRealName
open FiniteOverwrite
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem overwrite_generic (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : AtomicForcing.GroundGeneric M
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter A))) (s : List Bool) :
    AtomicForcing.GroundGeneric M
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter (overwrite s A))) := by
  sorry

end TuringRigidity.GroundPrefixOverwrite

end OAI
end
