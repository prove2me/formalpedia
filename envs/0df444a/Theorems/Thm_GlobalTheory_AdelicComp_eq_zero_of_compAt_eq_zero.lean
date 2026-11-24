-- Prove2me | Theorems.Thm_GlobalTheory_AdelicComp_eq_zero_of_compAt_eq_zero
-- name    : GlobalTheory.AdelicComp.eq_zero_of_compAt_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:54:14.845366+00:00
-- url     : https://prove2.me/theorems/da420889-c3fe-4bbe-8ab5-a4f3904d4935
-- title:
--   Adelic Comp: eq zero of comp At eq zero
-- statement:
--   The Adelic Comp construction uses the eq zero of comp At eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfCompAtEqZero.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EqZeroOfCompAtEqZero.lean#L34-L46

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCompAtEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open GlobalTheory GlobalTheory.AdelicComp

theorem GlobalTheory.AdelicComp.eq_zero_of_compAt_eq_zero :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (z : AL L), (∀ w, compAt L w z = 0) → z = 0 := by sorry
