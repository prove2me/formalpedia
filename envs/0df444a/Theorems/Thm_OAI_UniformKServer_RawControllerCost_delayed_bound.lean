-- Prove2me | Theorems.Thm_OAI_UniformKServer_RawControllerCost_delayed_bound
-- name    : OAI.UniformKServer.RawControllerCost.delayed_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:59:01.931204+00:00
-- url     : https://prove2.me/theorems/84864d81-10ad-4129-854e-532bfc2d876e
-- title:
--   OAI.UniformKServer.RawControllerCost.delayed_bound: intermediate lemma from OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniformKServer.RawControllerCost.delayed_bound` of [lean/OAI/Combinatorics/UniformKServer/RawControllerCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/RawControllerCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniformKServer.RawControllerCost`, with `open RawArithmetic RawCertificate EpochExpectation`):
--
--   ```lean
--   theorem delayed_bound (s : Configuration n k) (delay : ℕ) :
--       ∃B : ℝ,0≤B ∧ ∀w : List (Fin n),delayed hkn d draw hd v hv s delay w≤
--         OffsetInstance.coefficient mult*(Real.log (k+1))^2*offlineCost d s w+B
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniformKServer.OffsetInstance.coefficient`, `OAI.UniformKServer.RawArithmetic.Q`, `OAI.UniformKServer.RawArithmetic.value`, `OAI.UniformKServer.RawCertificate.Certificate`, `OAI.UniformKServer.RawCertificate.verify` and `OAI.UniformKServer.RawTable.dist` (definitions bundle `Q220Uk002` of this split); `OAI.UniformKServer.PartitionTree.absoluteRate` (definitions bundle `Q220Uk006` of this split); `OAI.UniformKServer.RawControllerCost.delayed` (definitions bundle `Q220Uk008` of this split); `OAI.UniformKServer.Configuration`, `OAI.UniformKServer.RationalMetric` and `OAI.UniformKServer.offlineCost` (the published bundle `Def_UniformKServer`).
--
--   **Used by.** The proof of `OAI.UniformKServer.uniform_squared_logarithmic_main` of this split imports it.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/RawControllerCost.lean (declaration OAI.UniformKServer.RawControllerCost.delayed_bound)

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk008

section

attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

namespace UniformKServer.RawControllerCost
open RawArithmetic RawCertificate EpochExpectation
variable {n k mult : ℕ} [NeZero k] (hk : 2≤k) (hkn : k≤n)
  (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n) (draw : List Q)
  (hd : ∀x y : Fin n,value (RawTable.dist n draw x.val y.val)=d.distance x y)
  (v : Certificate) (hv : verify mult (n,k,draw) v=true)

include hk hm hd hv in
theorem delayed_bound (s : Configuration n k) (delay : ℕ) :
    ∃B : ℝ,0≤B ∧ ∀w : List (Fin n),delayed hkn d draw hd v hv s delay w≤
      OffsetInstance.coefficient mult*(Real.log (k+1))^2*offlineCost d s w+B := by
  sorry

end UniformKServer.RawControllerCost

end

end

end OAI
end
