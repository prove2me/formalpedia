-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_bucket_support_original
-- name    : OAI.NuclearUltrapower.SOS.bucket_support_original
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:56:21.422313+00:00
-- url     : https://prove2.me/theorems/ac3f2b79-8ea0-49d7-af09-57cbf21c48bd
-- title:
--   OAI.NuclearUltrapower.SOS.bucket_support_original: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.bucket_support_original` of [lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS`):
--
--   ```lean
--   theorem bucket_support_original (le : α → α → Bool)
--       (original : List (Poly α)) (buckets : List (List (Poly α)))
--       (hnorm : original.map (normalize le) = buckets.map (fun r => normalize le r.flatten))
--       (b : ℕ) {m : α}
--       (hm : m ∈ (normalize le (buckets.flatMap (fun r => r.getD b []))).map Prod.fst) :
--       m ∈ original.flatten.map Prod.fst
--   ```
--
--   **Definitions.** The statement is written with `OAI.NuclearUltrapower.SOS.Poly` (definitions bundle `OAIQ019N000` of this split); `OAI.NuclearUltrapower.SOS.normalize` (definitions bundle `OAIQ019N047` of this split).
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.residual_good` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean (declaration OAI.NuclearUltrapower.SOS.bucket_support_original)

import Mathlib
import Definitions.Def_OAIQ019N047

section

attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace NuclearUltrapower.SOS
variable {α : Type*} [DecidableEq α]

theorem bucket_support_original (le : α → α → Bool)
    (original : List (Poly α)) (buckets : List (List (Poly α)))
    (hnorm : original.map (normalize le) = buckets.map (fun r => normalize le r.flatten))
    (b : ℕ) {m : α}
    (hm : m ∈ (normalize le (buckets.flatMap (fun r => r.getD b []))).map Prod.fst) :
    m ∈ original.flatten.map Prod.fst := by
  sorry
end NuclearUltrapower.SOS

end

end OAI
end
