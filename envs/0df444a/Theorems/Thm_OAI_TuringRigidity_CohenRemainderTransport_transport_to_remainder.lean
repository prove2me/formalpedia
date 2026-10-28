-- Prove2me | Theorems.Thm_OAI_TuringRigidity_CohenRemainderTransport_transport_to_remainder
-- name    : OAI.TuringRigidity.CohenRemainderTransport.transport_to_remainder
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:36:24.534622+00:00
-- url     : https://prove2.me/theorems/539e4a91-c562-4832-9f2d-f71970f32dc5
-- title:
--   OAI.TuringRigidity.CohenRemainderTransport.transport_to_remainder: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.CohenRemainderTransport.transport_to_remainder` of [lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenRemainderTransport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenRemainderTransport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.CohenRemainderTransport`, with `open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset InternalCountableOrdinals`):
--
--   ```lean
--   theorem transport_to_remainder (M N K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
--       (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
--       (hK : FirstUncountable M K) (hC : C ∈ M) (hCK : C ⊆ K)
--       (hct : C = ∅ ∨ InternallyCountable M C)
--       (U : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
--       (hU : AtomicForcing.GroundGeneric N U) :
--       ∃ R : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega))),
--         AtomicForcing.GroundGeneric N R ∧
--           genericExtensionSet N (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega)) R.carrier =
--             genericExtensionSet N (conditions (ZFSet.prod K ZFSet.omega)) U.carrier
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.AtomicForcing.GroundGeneric`, `OAI.TuringRigidity.CountableForcing.GenericFilter`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive`, `OAI.TuringRigidity.TransitiveNameModel.genericExtensionSet` and `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.collapsePreorder` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.InternallyCountable` and `OAI.TuringRigidity.InternalCountableOrdinals.FirstUncountable` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.CohenGroundPoset.conditions` (definitions bundle `OAIQ064A003` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.real_hull_generic_column_realizes` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/CohenForcing/CohenRemainderTransport.lean (declaration OAI.TuringRigidity.CohenRemainderTransport.transport_to_remainder)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A002
import Definitions.Def_OAIQ064A003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenRemainderTransport
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset InternalCountableOrdinals
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem transport_to_remainder (M N K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hK : FirstUncountable M K) (hC : C ∈ M) (hCK : C ⊆ K)
    (hct : C = ∅ ∨ InternallyCountable M C)
    (U : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hU : AtomicForcing.GroundGeneric N U) :
    ∃ R : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega))),
      AtomicForcing.GroundGeneric N R ∧
        genericExtensionSet N (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega)) R.carrier =
          genericExtensionSet N (conditions (ZFSet.prod K ZFSet.omega)) U.carrier := by
  sorry

end TuringRigidity.CohenRemainderTransport

end OAI
end
