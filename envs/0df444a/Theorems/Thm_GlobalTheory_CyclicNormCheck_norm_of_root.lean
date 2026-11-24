-- Prove2me | Theorems.Thm_GlobalTheory_CyclicNormCheck_norm_of_root
-- name    : GlobalTheory.CyclicNormCheck.norm_of_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:00.426605+00:00
-- url     : https://prove2.me/theorems/db61dbed-09f5-4f04-a163-864905ca5d12
-- title:
--   Cyclic Norm Check: norm of root
-- statement:
--   The Cyclic Norm Check construction uses the norm of root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AdelicSplittingExamples/LocalConditionsOfGlobal.lean#L32-L35

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CyclicNormPrinciple
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AdelicSplittingExamples_LocalConditionsOfGlobal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.CyclicNormCheck

theorem GlobalTheory.CyclicNormCheck.norm_of_root {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] {a r : K} (h : r ^ Module.finrank F E = a) :
    ∃ y : K ⊗[F] E, Algebra.norm K y = a := by sorry
