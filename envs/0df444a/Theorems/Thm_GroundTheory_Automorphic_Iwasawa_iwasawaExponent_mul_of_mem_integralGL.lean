-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawaExponent_mul_of_mem_integralGL
-- name    : GroundTheory.Automorphic.Iwasawa.iwasawaExponent_mul_of_mem_integralGL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:52.091811+00:00
-- url     : https://prove2.me/theorems/2ffd1134-0202-4a43-a956-e7fe40eca96a
-- title:
--   Iwasawa: iwasawa Exponent mul of mem integral GL
-- statement:
--   The Iwasawa construction uses the iwasawa Exponent mul of mem integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L463-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L463-L467

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Iwasawa.iwasawaExponent_mul_of_mem_integralGL (g : GL (Fin n) F) {k : GL (Fin n) F}
    (hk : k ∈ integralGL F n) : iwasawaExponent F n (g * k) = iwasawaExponent F n g := by sorry
