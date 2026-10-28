-- Prove2me | Theorems.Thm_OAI_KaplanskyConsequences_QuasiValue_ultra_polar_corner
-- name    : OAI.KaplanskyConsequences.QuasiValue.ultra_polar_corner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T15:37:46.658598+00:00
-- url     : https://prove2.me/theorems/426dbe82-0bbc-4733-9275-47e4f8718b97
-- title:
--   OAI.KaplanskyConsequences.QuasiValue.ultra_polar_corner: intermediate lemma from OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KaplanskyConsequences.QuasiValue.ultra_polar_corner` of [lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/Polar.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/Polar.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KaplanskyConsequences.QuasiValue`, with `open Filter Topology`, `open scoped ComplexOrder ENNReal`):
--
--   ```lean
--   lemma ultra_polar_corner (x p q : V.UltraQuotient u) (hp : IsStarProjection p)
--       (hxp : x*p=x) (hqx : q*x=x) :
--       ∃ v : V.UltraQuotient u, IsPartialIsometry v ∧
--         v*CFC.sqrt (star x*x)=x ∧ q*v=v ∧ v*p=v
--   ```
--
--   **Definitions.** The statement is written with `OAI.KaplanskyConsequences.IsPartialIsometry`, `OAI.KaplanskyConsequences.QuasiValue`, `OAI.KaplanskyConsequences.ClosedStarIdeal.instRingQuotient`, `OAI.KaplanskyConsequences.ClosedStarIdeal.instStarQuotient`, `OAI.KaplanskyConsequences.ClosedStarIdeal.instStarRingQuotient`, `OAI.KaplanskyConsequences.ClosedStarIdeal.submodule` and `OAI.KaplanskyConsequences.QuasiValue.nullIdeal` (definitions bundle `OAIQ15Sf004` of this split); `OAI.Kaplansky.boundedProductCStarAlgebra` (definitions bundle `OAIQ15Sf007` of this split); `OAI.KaplanskyConsequences.ClosedStarIdeal.quotientCStarAlgebra` (definitions bundle `OAIQ15Sf008` of this split); `OAI.KaplanskyConsequences.QuasiValue.Sequences` and `OAI.KaplanskyConsequences.QuasiValue.ultra` (definitions bundle `OAIQ15Sf010` of this split); `OAI.KaplanskyConsequences.QuasiValue.UltraQuotient`, `OAI.KaplanskyConsequences.QuasiValue.seq_nontrivial`,  (definitions bundle `OAIQ15Sf012` of this split).
--
--   **Used by.** The proof of `OAI.KaplanskyConsequences.QuasiValue.ultra_unitary_polar` of this split imports it.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/Polar.lean (declaration OAI.KaplanskyConsequences.QuasiValue.ultra_polar_corner)

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
open scoped ComplexOrder ENNReal
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealSMulComm_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealTower_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealCFC_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraNonnegSpectrum_p0
include hu in

lemma ultra_polar_corner (x p q : V.UltraQuotient u) (hp : IsStarProjection p)
    (hxp : x*p=x) (hqx : q*x=x) :
    ∃ v : V.UltraQuotient u, IsPartialIsometry v ∧
      v*CFC.sqrt (star x*x)=x ∧ q*v=v ∧ v*p=v := by
  sorry

end KaplanskyConsequences.QuasiValue

end

end OAI
end
