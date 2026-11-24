-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_compactOpen_psiN_trivial
-- name    : GroundTheory.Automorphic.Whittaker.exists_compactOpen_psiN_trivial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:41.171131+00:00
-- url     : https://prove2.me/theorems/0aa6555e-ecad-4d07-86e5-bed065678f91
-- title:
--   Whittaker: exists compact Open psi N trivial
-- statement:
--   The Whittaker construction uses the exists compact Open psi N trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L566-L609
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L566-L609

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
open ValuativeRel Topology
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

theorem GroundTheory.Automorphic.Whittaker.exists_compactOpen_psiN_trivial {ψ₀ : AddChar F ℂ} (hψ : Continuous ψ₀) :
    ∃ K : Subgroup (Iwasawa.unipotent F n), IsCompact (K : Set (Iwasawa.unipotent F n)) ∧
      IsOpen (K : Set (Iwasawa.unipotent F n)) ∧ ∀ k ∈ K, psiN ψ₀ (k : GL (Fin n) F) = 1 := by sorry
