-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_iwasawaExponent_torusPow
-- name    : GroundTheory.Automorphic.Iwasawa.iwasawaExponent_torusPow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:36:14.398655+00:00
-- url     : https://prove2.me/theorems/3893a786-dac9-429d-87bb-3afc908a3d8c
-- title:
--   Iwasawa: iwasawa Exponent torus Pow
-- statement:
--   The Iwasawa construction uses the iwasawa Exponent torus Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L460-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L460-L461

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

theorem GroundTheory.Automorphic.Iwasawa.iwasawaExponent_torusPow (l : Fin n → ℤ) : iwasawaExponent F n (torusPow F n l) = l := by sorry
