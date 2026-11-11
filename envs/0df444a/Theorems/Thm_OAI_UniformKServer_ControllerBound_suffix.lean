-- Prove2me | Theorems.Thm_OAI_UniformKServer_ControllerBound_suffix
-- name    : OAI.UniformKServer.ControllerBound.suffix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:00:07.327437+00:00
-- url     : https://prove2.me/theorems/9e32cf8c-88fd-4af4-a793-fe6de4a5ae90
-- title:
--   OAI.UniformKServer.ControllerBound.suffix: intermediate lemma from OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniformKServer.ControllerBound.suffix` of [lean/OAI/Combinatorics/UniformKServer/ControllerBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/ControllerBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniformKServer.ControllerBound`, with `open EpochShadow EpochExpectation EpochPartition TapeController`):
--
--   ```lean
--   theorem suffix (hR : 0<R) (hE : 0≤E)
--       (hpay : (2*A+1)*k*D+2*E+2*D≤(2*A+4)*R*δ)
--       (pre w : List (Fin n)) (original actual : Configuration n k) :
--       TapeController.expected (NeZero.pos k) hR d u N hN (TapeController.initial (M:=M) hR u) actual w≤
--         (4*A+4)*offlineCost d original (pre++w)+((2*A+1)*k*D+2*E+2*D)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniformKServer.horizon`, `OAI.UniformKServer.BitSampling.mean` and `OAI.UniformKServer.BitSampling.runCost` (definitions bundle `Q220Uk002` of this split); `OAI.UniformKServer.EpochExpectation.BState`, `OAI.UniformKServer.EpochExpectation.charge`, `OAI.UniformKServer.EpochExpectation.next` and `OAI.UniformKServer.TapeController.initial` (definitions bundle `Q220Uk005` of this split); `OAI.UniformKServer.TapeController.expected` (definitions bundle `Q220Uk008` of this split); `OAI.UniformKServer.Configuration`, `OAI.UniformKServer.RationalMetric` and `OAI.UniformKServer.offlineCost` (the published bundle `Def_UniformKServer`).
--
--   **Used by.** The proof of `OAI.UniformKServer.RawControllerCost.delayed_bound` of this split imports it.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/ControllerBound.lean (declaration OAI.UniformKServer.ControllerBound.suffix)

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk008

section

attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

namespace UniformKServer.ControllerBound
open EpochShadow EpochExpectation EpochPartition TapeController
variable {n k b M R : ℕ} [NeZero k] (hk2 : 2≤k) (d : RationalMetric n)
  (u : Configuration n k) (hu : Function.Injective u)
  (N : BState n k→Fin n→Fin k→ℕ) (hN : ∀s r,∑j,N s r j=2^b)
  (hLazy : ∀s r j,(∃i,s.2 i=r)→s.2 j≠r→N s r j=0)
  (D δ A E : ℝ) (hD : 0≤D) (hδ : 0≤δ) (hA : 0≤A)
  (hdiam : ∀x y,(d.distance x y:ℝ)≤D)
  (hsep : ∀x y,x≠y→δ≤(d.distance x y:ℝ))
  (hcap : R*(k+1)*D≤(M+1)*δ)
  (hTable : ∀w : List (Fin n),w.length≤horizon k M→
    BitSampling.mean (BitSampling.runCost N hN next (charge d) ([],u) w)≤
      A*offlineCost d u w+E+D)

include hk2 hu hLazy hD hδ hA hdiam hsep hcap hTable in
theorem suffix (hR : 0<R) (hE : 0≤E)
    (hpay : (2*A+1)*k*D+2*E+2*D≤(2*A+4)*R*δ)
    (pre w : List (Fin n)) (original actual : Configuration n k) :
    TapeController.expected (NeZero.pos k) hR d u N hN (TapeController.initial (M:=M) hR u) actual w≤
      (4*A+4)*offlineCost d original (pre++w)+((2*A+1)*k*D+2*E+2*D) := by
  sorry

end UniformKServer.ControllerBound

end

end

end OAI
end
