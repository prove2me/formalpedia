-- Prove2me | Theorems.Thm_OAI_ArExplicit_Statement_fullStatement_of_mainConclusions
-- name    : OAI.ArExplicit.Statement.fullStatement_of_mainConclusions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T15:21:14.695988+00:00
-- url     : https://prove2.me/theorems/5cf6ede0-616e-456d-b175-67bfa3de39f1
-- title:
--   OAI.ArExplicit.Statement.fullStatement_of_mainConclusions: intermediate lemma from OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ArExplicit.Statement.fullStatement_of_mainConclusions` of [lean/OAI/Algebra/AuslanderReiten/StatementEquivalence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/StatementEquivalence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ArExplicit.Statement`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem fullStatement_of_mainConclusions (c : ArExplicit.Candidate)
--       (h : ArExplicit.MainConclusions ArExplicit.BaseField c.R c.M) : FullStatement.{v}
--   ```
--
--   **Definitions.** The statement is written with `OAI.ArExplicit.BaseField` and `OAI.ArExplicit.ParameterRing` (definitions bundle `OAIQ031A001` of this split); `OAI.ArExplicit.MainConclusions` (definitions bundle `OAIQ031A019` of this split); `OAI.ArExplicit.Candidate` (definitions bundle `OAIQ031A038` of this split); `OAI.ArExplicit.Statement.FullStatement` (the published bundle `Def_AuslanderReiten`).
--
--   **Used by.** The proof of `OAI.ArExplicit.Statement.main` of this split imports it.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/StatementEquivalence.lean (declaration OAI.ArExplicit.Statement.fullStatement_of_mainConclusions)

import Mathlib
import Definitions.Def_AuslanderReiten
import Definitions.Def_OAIQ031A019
import Definitions.Def_OAIQ031A038

section

attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.Statement
universe u v

theorem fullStatement_of_mainConclusions (c : ArExplicit.Candidate)
    (h : ArExplicit.MainConclusions ArExplicit.BaseField c.R c.M) : FullStatement.{v} := by
  sorry

end ArExplicit.Statement

end

end OAI
end
