-- Prove2me | Theorems.Thm_OAI_BorsukNine_Admissible_no_free_ridge
-- name    : OAI.BorsukNine.Admissible.no_free_ridge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:44:07.107299+00:00
-- url     : https://prove2.me/theorems/8c8de917-a3f7-4968-8652-7326e24e64d9
-- title:
--   OAI.BorsukNine.Admissible.no_free_ridge: intermediate lemma from OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BorsukNine.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion (result family 156)*, OpenAI Math Release, September 23, 2026, result family 156, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BorsukNine.Admissible.no_free_ridge` of [lean/OAI/Geometry/Borsuk/LocalParity/NoFreeRidge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/LocalParity/NoFreeRidge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BorsukNine`, with `open Set MeasureTheory`, `open Set SimplicialChains`, `open scoped RealInnerProductSpace`):
--
--   ```lean
--   lemma Admissible.no_free_ridge {f : E → ι → ℝ} (hf : Admissible f)
--       (hk : 0 < k) (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
--       (hn : 1 < Fintype.card ι) {I U : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
--       (hI : I.card = k+1) (hUI : U ⊆ I) (hU : U.card = k)
--       (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
--       {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i) :
--       ∃ u : E, ‖u‖ = 1 ∧ U ⊆ positiveSupport f u ∧ ¬ positiveSupport f u ⊆ I
--   ```
--
--   **Definitions.** The statement is written with `OAI.BorsukNine.Admissible`, `OAI.BorsukNine.UpperTriangle` and `OAI.BorsukNine.positiveSupport` (definitions bundle `OAIQ058B000` of this split).
--
--   **Used by.** The proofs of `OAI.BorsukNine.Admissible.tetra_no_free_triangle` and `OAI.BorsukNine.main_theorem` of this split import it.
-- source:
--   OpenAI, A nine-dimensional counterexample to Borsuk's covering assertion (result family 156), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 156; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/LocalParity/NoFreeRidge.lean (declaration OAI.BorsukNine.Admissible.no_free_ridge)

import Mathlib
import Definitions.Def_OAIQ058B000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set SimplicialChains
open scoped RealInnerProductSpace
section NoFreeRidge
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

lemma Admissible.no_free_ridge {f : E → ι → ℝ} (hf : Admissible f)
    (hk : 0 < k) (hdim : Fintype.card (UpperTriangle (Fin (k+1))) = Fintype.card ι)
    (hn : 1 < Fintype.card ι) {I U : Finset ι} [Nonempty ↥(Iᶜ : Finset ι)]
    (hI : I.card = k+1) (hUI : U ⊆ I) (hU : U.card = k)
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ u : E, ‖u‖ = 1 ∧ U ⊆ positiveSupport f u ∧ ¬ positiveSupport f u ⊆ I := by
  sorry
end NoFreeRidge
end BorsukNine

end OAI
end
