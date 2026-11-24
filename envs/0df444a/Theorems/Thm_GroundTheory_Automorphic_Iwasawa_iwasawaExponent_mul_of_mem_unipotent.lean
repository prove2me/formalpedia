-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawaExponent_mul_of_mem_unipotent
-- name    : GroundTheory.Automorphic.Iwasawa.iwasawaExponent_mul_of_mem_unipotent
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:02.384859+00:00
-- url     : https://prove2.me/theorems/7aaf55eb-4227-4adc-a977-a6daa6574214
-- title:
--   Iwasawa: iwasawa Exponent mul of mem unipotent
-- statement:
--   The Iwasawa construction uses the iwasawa Exponent mul of mem unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L469-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L469-L473

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

theorem GroundTheory.Automorphic.Iwasawa.iwasawaExponent_mul_of_mem_unipotent {u : GL (Fin n) F} (hu : u ∈ unipotent F n)
    (g : GL (Fin n) F) : iwasawaExponent F n (u * g) = iwasawaExponent F n g := by sorry
