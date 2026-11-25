-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawaExponent_eq
-- name    : GroundTheory.Automorphic.Iwasawa.iwasawaExponent_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:26.474342+00:00
-- url     : https://prove2.me/theorems/58a1ba43-889c-4a71-827b-94f44d0902c7
-- title:
--   Iwasawa: iwasawa Exponent eq
-- statement:
--   The Iwasawa construction uses the iwasawa Exponent eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L454-L458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L454-L458

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

theorem GroundTheory.Automorphic.Iwasawa.iwasawaExponent_eq {u k : GL (Fin n) F} {l : Fin n → ℤ} (hu : u ∈ unipotent F n)
    (hk : k ∈ integralGL F n) : iwasawaExponent F n (u * torusPow F n l * k) = l := by sorry
