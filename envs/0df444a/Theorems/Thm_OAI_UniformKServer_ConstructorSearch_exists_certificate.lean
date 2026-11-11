-- Prove2me | Theorems.Thm_OAI_UniformKServer_ConstructorSearch_exists_certificate
-- name    : OAI.UniformKServer.ConstructorSearch.exists_certificate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:58:02.676258+00:00
-- url     : https://prove2.me/theorems/61ab451a-9948-424e-8449-d9cf4ed92c01
-- title:
--   OAI.UniformKServer.ConstructorSearch.exists_certificate: intermediate lemma from OpenAI, Uniform computation of the squared-logarithmic k-server bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniformKServer.uniform_squared_logarithmic_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform computation of the squared-logarithmic k-server bound*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniformKServer.ConstructorSearch.exists_certificate` of [lean/OAI/Combinatorics/UniformKServer/ConstructorSearch.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/ConstructorSearch.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniformKServer.ConstructorSearch`, with `open RawCertificate`, `open scoped Classical`):
--
--   ```lean
--   theorem exists_certificate {n k : ℕ} [NeZero k] (hn : 2≤n) (hk : 2≤k) (hkn : k≤n)
--       (mult : ℕ) (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n)
--       (draw : List RawArithmetic.Q)
--       (hd : ∀x y : Fin n,RawArithmetic.value (RawTable.dist n draw x.val y.val)=d.distance x y) :
--       ∃v : Cert,verify mult (n,k,draw) v=true
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniformKServer.RawArithmetic.Q`, `OAI.UniformKServer.RawArithmetic.value` and `OAI.UniformKServer.RawTable.dist` (definitions bundle `Q220Uk002` of this split); `OAI.UniformKServer.ConstructorSearch.Cert` and `OAI.UniformKServer.ConstructorSearch.verify` (definitions bundle `Q220Uk005` of this split); `OAI.UniformKServer.PartitionTree.absoluteRate` (definitions bundle `Q220Uk006` of this split); `OAI.UniformKServer.RationalMetric` (the published bundle `Def_UniformKServer`).
--
--   **Used by.** The proof of `OAI.UniformKServer.uniform_squared_logarithmic_main` of this split imports it.
-- source:
--   OpenAI, Uniform computation of the squared-logarithmic k-server bound, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026/Uniform-computation-of-the-squared-logarithmic-k-server-bound-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/UniformKServer/ConstructorSearch.lean (declaration OAI.UniformKServer.ConstructorSearch.exists_certificate)

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk005
import Definitions.Def_Q220Uk006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ConstructorSearch
open RawCertificate
open scoped Classical

theorem exists_certificate {n k : ℕ} [NeZero k] (hn : 2≤n) (hk : 2≤k) (hkn : k≤n)
    (mult : ℕ) (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n)
    (draw : List RawArithmetic.Q)
    (hd : ∀x y : Fin n,RawArithmetic.value (RawTable.dist n draw x.val y.val)=d.distance x y) :
    ∃v : Cert,verify mult (n,k,draw) v=true := by
  sorry

end UniformKServer.ConstructorSearch

end

end OAI
end
