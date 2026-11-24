-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawa_unique
-- name    : GroundTheory.Automorphic.Iwasawa.iwasawa_unique
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:11.004771+00:00
-- url     : https://prove2.me/theorems/cbc98719-2401-4ffb-8bca-73637f564b66
-- title:
--   Iwasawa: iwasawa unique
-- statement:
--   The Iwasawa construction uses the iwasawa unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L404-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L404-L443

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

theorem GroundTheory.Automorphic.Iwasawa.iwasawa_unique {u u' k k' : GL (Fin n) F} {l l' : Fin n → ℤ}
    (hu : u ∈ unipotent F n) (hu' : u' ∈ unipotent F n)
    (hk : k ∈ integralGL F n) (hk' : k' ∈ integralGL F n)
    (h : u * torusPow F n l * k = u' * torusPow F n l' * k') :
    l = l' ∧ ∃ m ∈ unipotent F n ⊓ integralGL F n,
      u' = u * torusPow F n l * m * (torusPow F n l)⁻¹ := by sorry
