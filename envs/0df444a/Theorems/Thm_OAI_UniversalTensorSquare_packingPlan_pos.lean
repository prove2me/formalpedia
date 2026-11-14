-- Prove2me | Theorems.Thm_OAI_UniversalTensorSquare_packingPlan_pos
-- name    : OAI.UniversalTensorSquare.packingPlan_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T18:11:31.285802+00:00
-- url     : https://prove2.me/theorems/394eb60e-8e14-4c96-9e7c-c730053ea977
-- title:
--   OAI.UniversalTensorSquare.packingPlan_pos: intermediate lemma from OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniversalTensorSquare.packingPlan_pos` of [lean/OAI/RepresentationTheory/UniversalSquare/Balance/PackingPlans.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/PackingPlans.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniversalTensorSquare`, with `open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns`):
--
--   ```lean
--   theorem packingPlan_pos {n d : ℕ} (p : PackingPlan) {lam μ : YoungDiagram}
--       (hv : p.Valid d) (hb : BandsValid p.bands) (hheight : lam.colLen 0 = d)
--       (hc : p.columns.Perm lam.transpose.rowLens) (hp : ∀ x ∈ p.parts, 0 < x)
--       (a : Tableau n lam) (t : Tableau n μ)
--       (hd : Dominates μ (columnShape p.parts).transpose) : 0 < kronecker a a t
--   ```
--
--   **Definitions.** The statement is written with `OAI.Saxl.Balance.BandsValid` (definitions bundle `OAIQ259US000` of this split); `OAI.Saxl.Dominates`, `OAI.Saxl.Balance.PackingPlan`, `OAI.Saxl.Columns.columnShape`, `OAI.Saxl.Balance.PackingPlan.Valid`, `OAI.Saxl.Balance.PackingPlan.bands`, `OAI.Saxl.Balance.PackingPlan.columns` and `OAI.Saxl.Balance.PackingPlan.parts` (definitions bundle `OAIQ259US001` of this split); `OAI.Saxl.Tableau` and `OAI.Saxl.kronecker` (the published bundle `Def_UniversalTensorSquares`).
--
--   **Used by.** The proofs of `OAI.UniversalTensorSquare.candidate_residual_pos`, `OAI.UniversalTensorSquare.degreeCones151`, `OAI.UniversalTensorSquare.degree_pos112`, `OAI.UniversalTensorSquare.degree_pos118`, `OAI.UniversalTensorSquare.degree_pos12`, `OAI.UniversalTensorSquare.degree_pos14`, `OAI.UniversalTensorSquare.degree_pos16`, `OAI.UniversalTensorSquare.degree_pos18`, `OAI.UniversalTensorSquare.degree_pos19`, `OAI.UniversalTensorSquare.degree_pos20`, `OAI.UniversalTensorSquare.degree_pos22`, `OAI.UniversalTensorSquare.degree_pos24`, `OAI.UniversalTensorSquare.degree_pos26`, `OAI.UniversalTensorSquare.degree_pos31`, `OAI.UniversalTensorSquare.degree_pos35`, `OAI.UniversalTensorSquare.degree_pos37`, `OAI.UniversalTensorSquare.degree_pos38`, `OAI.UniversalTensorSquare.degree_pos39`, `OAI.UniversalTensorSquare.degree_pos41`, `OAI.UniversalTensorSquare.degree_pos43`, `OAI.UniversalTensorSquare.degree_pos46`, `OAI.UniversalTensorSquare.degree_pos50`, `OAI.UniversalTensorSquare.degree_pos54`, `OAI.UniversalTensorSquare.degree_pos57`, `OAI.UniversalTensorSquare.degree_pos58`, `OAI.UniversalTensorSquare.degree_pos62`, `OAI.UniversalTensorSquare.degree_pos64`, `OAI.UniversalTensorSquare.degree_pos89`, `OAI.UniversalTensorSquare.exceptional_pos106`, `OAI.UniversalTensorSquare.exceptional_pos108`, `OAI.UniversalTensorSquare.exceptional_pos110`, `OAI.UniversalTensorSquare.exceptional_pos114`, `OAI.UniversalTensorSquare.exceptional_pos149`, `OAI.UniversalTensorSquare.exceptional_pos71`, `OAI.UniversalTensorSquare.exceptional_pos75`, `OAI.UniversalTensorSquare.exceptional_pos79`, `OAI.UniversalTensorSquare.exceptional_pos81`, `OAI.UniversalTensorSquare.exceptional_pos83`, `OAI.UniversalTensorSquare.exceptional_pos85`, `OAI.UniversalTensorSquare.exceptional_pos87`, `OAI.UniversalTensorSquare.universal_partition_exceptional` and `OAI.UniversalTensorSquare.universal_partition_le64` of this split import it.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/RepresentationTheory/UniversalSquare/Balance/PackingPlans.lean (declaration OAI.UniversalTensorSquare.packingPlan_pos)

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US000
import Definitions.Def_OAIQ259US001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns

theorem packingPlan_pos {n d : ℕ} (p : PackingPlan) {lam μ : YoungDiagram}
    (hv : p.Valid d) (hb : BandsValid p.bands) (hheight : lam.colLen 0 = d)
    (hc : p.columns.Perm lam.transpose.rowLens) (hp : ∀ x ∈ p.parts, 0 < x)
    (a : Tableau n lam) (t : Tableau n μ)
    (hd : Dominates μ (columnShape p.parts).transpose) : 0 < kronecker a a t := by
  sorry

end UniversalTensorSquare
end
end

end OAI
end
