-- Prove2me | Theorems.Thm_GlobalTheory_SplitComp_compAt_eq_zero
-- name    : GlobalTheory.SplitComp.compAt_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:17.9855+00:00
-- url     : https://prove2.me/theorems/07df4f45-d6e2-44fc-91d1-454da7a1694c
-- title:
--   Split Comp: comp At eq zero
-- statement:
--   The Split Comp construction uses the comp At eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRealAdd.lean#L47-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRealAdd.lean#L47-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct
open GlobalTheory GlobalTheory.SplitComp
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

theorem GlobalTheory.SplitComp.compAt_eq_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (z : AL L),
    s.proj z = 0 → s.proj (conjAL L z) = 0 → compAt L s.v z = 0 := by sorry
