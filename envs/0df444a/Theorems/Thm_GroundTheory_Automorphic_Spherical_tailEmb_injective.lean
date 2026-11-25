-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_tailEmb_injective
-- name    : GroundTheory.Automorphic.Spherical.tailEmb_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:32:53.820799+00:00
-- url     : https://prove2.me/theorems/6eac80d2-a7ab-47fc-af67-b730d3196daa
-- title:
--   Spherical: tail Emb injective
-- statement:
--   The Spherical construction uses the tail Emb injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L86-L90

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
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
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.Spherical.tailEmb_injective {m : ℕ} (hm : m ≤ n) : Function.Injective (tailEmb hm) := by sorry
