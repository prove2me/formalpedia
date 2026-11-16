-- Prove2me | Theorems.Thm_OAI_Saxl_Columns_contractionInteger_compact
-- name    : OAI.Saxl.Columns.contractionInteger_compact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-15T21:32:49.900957+00:00
-- url     : https://prove2.me/theorems/4e54aae7-5f47-406b-8ed1-7bbc6dbf82bc
-- title:
--   OAI.Saxl.Columns.contractionInteger_compact: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.Columns.contractionInteger_compact` of [lean/OAI/RepresentationTheory/UniversalSquare/Contraction/CompactDomainsCore.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/CompactDomainsCore.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl.Columns`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma contractionInteger_compact {n : ℕ} (rsA rsB rsT : List ℕ)
--       (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
--       (flag : Finset (ℕ × ℕ × ℕ)) :
--       contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
--         solveCompact n (.full rsT) (.full rsA) (.full rsB)
--           (certificateEdges rsA rsB rsT ea eb et) flag
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Columns.CompactDomains.full` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.Columns.certificateEdges`, `OAI.Saxl.Columns.contractionInteger` and `OAI.Saxl.Columns.solveCompact` (definitions bundle `OAIQ259US006` of this split).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.eightCertificate0`, `OAI.UniversalTensorSquare.eightCertificate10`, `OAI.UniversalTensorSquare.eightCertificate2`, `OAI.UniversalTensorSquare.eightCertificate4`, `OAI.UniversalTensorSquare.eightCertificate5`, `OAI.UniversalTensorSquare.eightCertificate7`, `OAI.UniversalTensorSquare.eightCertificate8`, `OAI.UniversalTensorSquare.eight_positive1`, `OAI.UniversalTensorSquare.eight_positive11`, `OAI.UniversalTensorSquare.eight_positive3`, `OAI.UniversalTensorSquare.eight_positive6` and `OAI.UniversalTensorSquare.eight_positive9` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Contraction/CompactDomainsCore.lean (declaration OAI.Saxl.Columns.contractionInteger_compact)

import Mathlib
import Definitions.Def_OAIQ259US006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators
namespace Saxl.Columns

lemma contractionInteger_compact {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (flag : Finset (ℕ × ℕ × ℕ)) :
    contractionInteger rsA rsB rsT ea eb et (fun r a b => if (r,a,b) ∈ flag then 1 else 0) =
      solveCompact n (.full rsT) (.full rsA) (.full rsB)
        (certificateEdges rsA rsB rsT ea eb et) flag := by
  sorry

end Saxl.Columns

end

end OAI
end
