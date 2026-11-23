-- Prove2me | Theorems.Thm_GlobalTheory_T_heckeChar_unramified_inverse_split_pair
-- name    : GlobalTheory.T.heckeChar_unramified_inverse_split_pair
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:11.256573+00:00
-- url     : https://prove2.me/theorems/bd97e161-e1e9-4ca8-b5e7-52c21f64d6f8
-- title:
--   T: hecke Char unramified inverse split pair
-- statement:
--   The T construction uses the hecke Char unramified inverse split pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPairStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeCharUnramifiedInverseSplitPairStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeCharUnramifiedInverseSplitPair
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeCharUnramifiedInverseSplitPairStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.heckeChar_unramified_inverse_split_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (v : HeightOneSpectrum (OF E)) (P P' : HeightOneSpectrum (𝓞 E)), TrivOnF χ → Splits v → Over P v → Over P' v → P ≠ P' → LevelLe χ P' 1 → UnrAt χ P → UnrAt χ P' ∧ val χ P' = (val χ P)⁻¹ := by sorry
