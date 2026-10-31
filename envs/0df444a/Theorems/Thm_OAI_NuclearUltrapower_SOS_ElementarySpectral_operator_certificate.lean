-- Prove2me | Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_operator_certificate
-- name    : OAI.NuclearUltrapower.SOS.ElementarySpectral.operator_certificate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T07:55:43.357078+00:00
-- url     : https://prove2.me/theorems/358568f8-9c6b-4f1f-be28-838865254e8e
-- title:
--   OAI.NuclearUltrapower.SOS.ElementarySpectral.operator_certificate: intermediate lemma from OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.NuclearUltrapower.SOS.ElementarySpectral.operator_certificate` of [lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.NuclearUltrapower.SOS.ElementarySpectral`, with `open scoped InnerProductSpace ComplexOrder`):
--
--   ```lean
--   theorem operator_certificate (D Q R : H →L[ℂ] H)
--       (h : R = (10000000000000 : ℤ) • (D*D) - (1000000000000 : ℤ) • D - (10 : ℤ) • Q) :
--       (10000000000000 : ℝ) • (D*D) - (1000000000000 : ℝ) • D = (10 : ℤ) • Q + R
--   ```
--
--   **Used by.** The proof of `OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate` of this split imports it.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/IntegralCertificate.lean (declaration OAI.NuclearUltrapower.SOS.ElementarySpectral.operator_certificate)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem operator_certificate (D Q R : H →L[ℂ] H)
    (h : R = (10000000000000 : ℤ) • (D*D) - (1000000000000 : ℤ) • D - (10 : ℤ) • Q) :
    (10000000000000 : ℝ) • (D*D) - (1000000000000 : ℝ) • D = (10 : ℤ) • Q + R := by
  sorry

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end
