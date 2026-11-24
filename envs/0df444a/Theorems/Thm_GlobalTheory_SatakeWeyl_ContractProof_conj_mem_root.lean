-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_ContractProof_conj_mem_root
-- name    : GlobalTheory.SatakeWeyl.ContractProof.conj_mem_root
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:27:51.797036+00:00
-- url     : https://prove2.me/theorems/538d2dad-5d01-4660-b995-9345d126eb4f
-- title:
--   Contract Proof: conj mem root
-- statement:
--   The Contract Proof construction uses the conj mem root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryDominantDiagonalConjugationContracts.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryDominantDiagonalConjugationContracts.lean#L45-L52

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDominantDiagonalConjugationContracts
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
noncomputable section
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.ContractProof
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.SatakeWeyl.ContractProof.conj_mem_root {ϖ : L} (h0 : ϖ ≠ 0) (γ : Fin r → ℕ) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (hg : g ∈ rootU σ γ) : s * g * s⁻¹ ∈ rootU σ γ := by sorry
