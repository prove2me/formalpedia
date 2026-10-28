-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_MachineCode_frozen_machine
-- name    : OAI.CommonBasesFPRAS.MachineCode.frozen_machine
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:26:19.269291+00:00
-- url     : https://prove2.me/theorems/e12203a6-672d-4f65-9a82-a5f59e603f5c
-- title:
--   OAI.CommonBasesFPRAS.MachineCode.frozen_machine: intermediate lemma from OpenAI, Approximate counting of common bases of two matroids
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.common_bases_fpras`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Approximate counting of common bases of two matroids*, OpenAI Math Release, September 23, 2026, result family 114, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CommonBasesFPRAS.MachineCode.frozen_machine` of [lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CommonBasesFPRAS.MachineCode`, with `open Expression`, `open scoped Classical`, `open Expression`, `open Expression`, `open scoped Classical`, `open Expression`, `open scoped Classical`, `open Expression`, `open Expression`, `open scoped Classical`, `open Expression`, `open scoped Classical`, `open Expression`, `open Expression Effect`, `open Expression`, `open scoped Classical`, `open Expression`, `open Expression Effect`, `open Expression`, `open Expression Effect`, `open Expression`, `open Expression`, `open Expression Effect`, `open Expression`, `open Expression`, `open Expression Effect`, `open scoped Classical`, `open Expression`, `open Expression`, `open scoped Classical`, `open Expression`):
--
--   ```lean
--   lemma frozen_machine (fp fq : SizePolynomial) (n r : ℕ)
--       (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n) (ε δ : ℚ)
--       (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
--       (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞)) (hε : 0<ε)
--       (hp : Safe O (fp.eval (masterParameter n r ε δ)) preambleCode (frozenValue n r ε δ))
--       (hq : ∀ w : BitWord (fairBitCount n ε δ),
--         Safe O (fq.eval (masterParameter n r ε δ)) postambleCode (rawValue n r ε δ w))
--       (B : ℕ) (hB : (totalResourcePoly fp fq).eval (masterParameter n r ε δ)≤B) :
--       ∃ (v : BitWord (fairBitCount n ε δ) → ℚ) (start : ℕ),
--         OutputCertificate r M₁ M₂ O ε δ v ∧ start+3*fairBitCount n ε δ+1≤B ∧
--         ∀ bits : ℕ → Bool,
--           let out := execution fprasBlock.code O (initialConfig 1 fprasBlock.size n r ε δ) bits B
--           out.output=some (v (physicalWord start (fairBitCount n ε δ) bits)) ∧
--             out.oracleCalls≤B ∧ out.bitOperations≤B
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.BitWord`, `OAI.CommonBasesFPRAS.fairBitCount`, `OAI.CommonBasesFPRAS.MachineCode.FrozenData`, `OAI.CommonBasesFPRAS.MachineCode.OutputCertificate`, `OAI.CommonBasesFPRAS.MachineCode.Safe`, `OAI.CommonBasesFPRAS.MachineCode.SizePolynomial`, `OAI.CommonBasesFPRAS.MachineCode.fprasBlock`, `OAI.CommonBasesFPRAS.MachineCode.frozenValue`, `OAI.CommonBasesFPRAS.MachineCode.masterParameter`, `OAI.CommonBasesFPRAS.MachineCode.physicalWord`, `OAI.CommonBasesFPRAS.MachineCode.rawValue`, `OAI.CommonBasesFPRAS.MachineCode.totalResourcePoly`, `OAI.CommonBasesFPRAS.MachineCode.Block`, `OAI.CommonBasesFPRAS.MachineCode.DataType`, `OAI.CommonBasesFPRAS.MachineCode.Expression.NN`, `OAI.CommonBasesFPRAS.MachineCode.Expression.PreparedData`, `OAI.CommonBasesFPRAS.MachineCode.Expression.RawData`, `OAI.CommonBasesFPRAS.MachineCode.Expression.postambleCode`, `OAI.CommonBasesFPRAS.MachineCode.Expression.preambleCode` and `OAI.CommonBasesFPRAS.MachineCode.SizePolynomial.eval` (definitions bundle `OAIQ2Mt000` of this split); `OAI.CommonBasesFPRAS.ExactOracles`, `OAI.CommonBasesFPRAS.IndependenceOracle`, `OAI.CommonBasesFPRAS.MachineConfig`, `OAI.CommonBasesFPRAS.execution` and `OAI.CommonBasesFPRAS.initialConfig` (the published bundle `Def_CommonBasesFPRAS`).
--
--   **Used by.** The proof of `OAI.common_bases_fpras` of this split imports it.
-- source:
--   OpenAI, Approximate counting of common bases of two matroids, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 114; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Approximate-counting-of-common-bases-of-two-matroids-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatroidCounting/MatroidCounting/CommonBases.lean (declaration OAI.CommonBasesFPRAS.MachineCode.frozen_machine)

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_OAIQ2Mt000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CommonBasesFPRAS

namespace MachineCode


open Expression

open Expression

open Expression

open Expression

open Expression

open Expression
end MachineCode

namespace MachineCode

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
open scoped Classical

open Expression

open Expression Effect

open Expression
open Expression Effect

open Expression

open Expression

open Expression Effect

open Expression

open Expression

open Expression Effect
open scoped Classical

open Expression

open Expression
open scoped Classical

open Expression

lemma frozen_machine (fp fq : SizePolynomial) (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (O : IndependenceOracle n) (ε δ : ℚ)
    (hO : ExactOracles M₁ M₂ O) (hE₁ : M₁.E=Set.univ) (hE₂ : M₂.E=Set.univ)
    (hr₁ : M₁.eRank=(r:ℕ∞)) (hr₂ : M₂.eRank=(r:ℕ∞)) (hε : 0<ε)
    (hp : Safe O (fp.eval (masterParameter n r ε δ)) preambleCode (frozenValue n r ε δ))
    (hq : ∀ w : BitWord (fairBitCount n ε δ),
      Safe O (fq.eval (masterParameter n r ε δ)) postambleCode (rawValue n r ε δ w))
    (B : ℕ) (hB : (totalResourcePoly fp fq).eval (masterParameter n r ε δ)≤B) :
    ∃ (v : BitWord (fairBitCount n ε δ) → ℚ) (start : ℕ),
      OutputCertificate r M₁ M₂ O ε δ v ∧ start+3*fairBitCount n ε δ+1≤B ∧
      ∀ bits : ℕ → Bool,
        let out := execution fprasBlock.code O (initialConfig 1 fprasBlock.size n r ε δ) bits B
        out.output=some (v (physicalWord start (fairBitCount n ε δ) bits)) ∧
          out.oracleCalls≤B ∧ out.bitOperations≤B := by
  sorry

open scoped Classical

end MachineCode
end CommonBasesFPRAS

open CommonBasesFPRAS CommonBasesFPRAS.MachineCode

end OAI
end
