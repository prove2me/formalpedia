-- Prove2me | Theorems.Thm_OAI_Saxl_young_orbit_map_uts
-- name    : OAI.Saxl.young_orbit_map_uts
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:10:22.761813+00:00
-- url     : https://prove2.me/theorems/ac482019-08fc-4952-a3e6-2bfa25fd3bb2
-- title:
--   OAI.Saxl.young_orbit_map_uts: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Saxl.young_orbit_map` of [lean/OAI/RepresentationTheory/Saxl/CyclicTensor.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/CyclicTensor.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Saxl`, with `open scoped TensorProduct`):
--
--   ```lean
--   theorem young_orbit_map_uts {n : ℕ} (θ τ : YoungDiagram) (t : Tableau n τ)
--       (hc : τ.card = θ.card) (hd : Dominates τ θ)
--       (w : Fin n → Fin (θ.colLen 0)) (e : Equiv.Perm (Fin (θ.colLen 0)))
--       (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j) :
--       ∃ F : Representation.IntertwiningMap (wordRep n (θ.colLen 0)) (spechtRep t),
--         F (Pi.single w 1) ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Dominates` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.Specht`, `OAI.Saxl.Tableau`, `OAI.Saxl.WordSpace`, `OAI.Saxl.spechtRep` and `OAI.Saxl.wordRep` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.Saxl.Balance.WordPacking.kronecker_pos` and `OAI.Saxl.dominated_support_uts` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/Saxl/CyclicTensor.lean (declaration OAI.Saxl.young_orbit_map)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY

namespace Saxl

theorem young_orbit_map_uts {n : ℕ} (θ τ : YoungDiagram) (t : Tableau n τ)
    (hc : τ.card = θ.card) (hd : Dominates τ θ)
    (w : Fin n → Fin (θ.colLen 0)) (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j) :
    ∃ F : Representation.IntertwiningMap (wordRep n (θ.colLen 0)) (spechtRep t),
      F (Pi.single w 1) ≠ 0 := by
  sorry

end Saxl

end

end OAI
end
