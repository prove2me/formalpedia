-- Prove2me | Theorems.Thm_OAI_TuringRigidity_ArithmeticFiniteTruthTransfer_source_equation_finite_family
-- name    : OAI.TuringRigidity.ArithmeticFiniteTruthTransfer.source_equation_finite_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:37:59.973385+00:00
-- url     : https://prove2.me/theorems/db3da921-66db-445e-9e53-68c4c123b1c6
-- title:
--   OAI.TuringRigidity.ArithmeticFiniteTruthTransfer.source_equation_finite_family: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.ArithmeticFiniteTruthTransfer.source_equation_finite_family` of [lean/OAI/Computability/DegreeRigidity/Computability/ArithmeticFiniteTruthTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Computability/ArithmeticFiniteTruthTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.ArithmeticFiniteTruthTransfer`, with `open UniformArithmetic ArithmeticPrefixForcing`, `open ShuffleRequirements FiniteShuffle GenericIdentity GenericTruth`, `open EncodedForcing (word)`):
--
--   ```lean
--   theorem source_equation_finite_family (p : OracleCode) (P : Oracle)
--       (hd : ∀ s : List Bool, ∃ H : Oracle,
--         Generic (fun _ => P) H ∧ Realizes s H ∧ SourceEquation p P (triple H)) :
--       ∃ E : PrefixPredicate, ArithmeticPrefix E ∧
--         (∀ n, DenseOpen (E (fun _ => P) n)) ∧
--         ∀ G : Oracle, GenericFor (E (fun _ => P)) G → SourceEquation p P (triple G)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.OracleCode`, `OAI.TuringRigidity.ArithmeticPrefixForcing.ArithmeticPrefix`, `OAI.TuringRigidity.ArithmeticPrefixForcing.Generic`, `OAI.TuringRigidity.ArithmeticPrefixForcing.PrefixPredicate`, `OAI.TuringRigidity.FiniteShuffle.DenseOpen`, `OAI.TuringRigidity.GenericTruth.triple` and `OAI.TuringRigidity.ShuffleRequirements.Realizes` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.ShuffleRequirements.GenericFor` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.GenericIdentity.SourceEquation` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Computability/ArithmeticFiniteTruthTransfer.lean (declaration OAI.TuringRigidity.ArithmeticFiniteTruthTransfer.source_equation_finite_family)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticFiniteTruthTransfer
open UniformArithmetic ArithmeticPrefixForcing
open ShuffleRequirements FiniteShuffle GenericIdentity GenericTruth
open EncodedForcing (word)

theorem source_equation_finite_family (p : OracleCode) (P : Oracle)
    (hd : ∀ s : List Bool, ∃ H : Oracle,
      Generic (fun _ => P) H ∧ Realizes s H ∧ SourceEquation p P (triple H)) :
    ∃ E : PrefixPredicate, ArithmeticPrefix E ∧
      (∀ n, DenseOpen (E (fun _ => P) n)) ∧
      ∀ G : Oracle, GenericFor (E (fun _ => P)) G → SourceEquation p P (triple G) := by
  sorry

end TuringRigidity.ArithmeticFiniteTruthTransfer

end OAI
end
