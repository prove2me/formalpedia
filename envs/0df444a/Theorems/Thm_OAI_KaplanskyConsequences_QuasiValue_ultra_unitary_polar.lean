-- Prove2me | Theorems.Thm_OAI_KaplanskyConsequences_QuasiValue_ultra_unitary_polar
-- name    : OAI.KaplanskyConsequences.QuasiValue.ultra_unitary_polar
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T15:41:02.644058+00:00
-- url     : https://prove2.me/theorems/1f672722-4e91-42e0-a193-c4524023665b
-- title:
--   OAI.KaplanskyConsequences.QuasiValue.ultra_unitary_polar: intermediate lemma from OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KaplanskyConsequences.QuasiValue.ultra_unitary_polar` of [lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/Unitary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/Unitary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KaplanskyConsequences.QuasiValue`, with `open Filter Topology`):
--
--   ```lean
--   lemma ultra_unitary_polar (x : V.UltraQuotient u) :
--       ∃ w : V.UltraQuotient u, star w*w=1 ∧ w*star w=1 ∧
--         w*CFC.sqrt (star x*x)=x
--   ```
--
--   **Definitions.** The statement is written with `OAI.KaplanskyConsequences.QuasiValue`, `OAI.KaplanskyConsequences.ClosedStarIdeal.instRingQuotient`, `OAI.KaplanskyConsequences.ClosedStarIdeal.instStarQuotient`, `OAI.KaplanskyConsequences.ClosedStarIdeal.instStarRingQuotient`, `OAI.KaplanskyConsequences.ClosedStarIdeal.submodule` and `OAI.KaplanskyConsequences.QuasiValue.nullIdeal` (definitions bundle `OAIQ15Sf004` of this split); `OAI.Kaplansky.boundedProductCStarAlgebra` (definitions bundle `OAIQ15Sf007` of this split); `OAI.KaplanskyConsequences.ClosedStarIdeal.quotientCStarAlgebra` (definitions bundle `OAIQ15Sf008` of this split); `OAI.KaplanskyConsequences.QuasiValue.Sequences` and `OAI.KaplanskyConsequences.QuasiValue.ultra` (definitions bundle `OAIQ15Sf010` of this split); `OAI.KaplanskyConsequences.QuasiValue.UltraQuotient`, `OAI.KaplanskyConsequences.QuasiValue.seq_nontrivial`,  (definitions bundle `OAIQ15Sf012` of this split).
--
--   **Used by.** The proof of `OAI.KaplanskyConsequences.simple_stablyFinite_traceless_exists` of this split imports it.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/Unitary.lean (declaration OAI.KaplanskyConsequences.QuasiValue.ultra_unitary_polar)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ15Sf012

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealSMulComm_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealTower_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealCFC_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraNonnegSpectrum_p0
include hu in
lemma ultra_unitary_polar (x : V.UltraQuotient u) :
    ∃ w : V.UltraQuotient u, star w*w=1 ∧ w*star w=1 ∧
      w*CFC.sqrt (star x*x)=x := by
  sorry

end KaplanskyConsequences.QuasiValue

end

end OAI
end
