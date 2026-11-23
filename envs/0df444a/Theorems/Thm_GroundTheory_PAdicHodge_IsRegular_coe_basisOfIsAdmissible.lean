-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_coe_basisOfIsAdmissible
-- name    : GroundTheory.PAdicHodge.IsRegular.coe_basisOfIsAdmissible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:06.013381+00:00
-- url     : https://prove2.me/theorems/fee8ece3-3c10-4ac8-970b-cec5d572b706
-- title:
--   Is Regular: coe basis Of Is Admissible
-- statement:
--   The Is Regular construction uses the coe basis Of Is Admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean#L342-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/Admissible.lean#L342-L345

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
open GroundTheory.PAdicHodge.IsRegular
variable {G F B : Type*} [Group G] [Field F] [CommRing B] [IsDomain B] [Algebra F B]
  [MulSemiringAction G B] [SMulCommClass G F B] (h : IsRegular G F B)
include h
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)

theorem GroundTheory.PAdicHodge.IsRegular.coe_basisOfIsAdmissible [FiniteDimensional F V] (hadm : IsAdmissible B ρ)
    {ι : Type*} [Fintype ι] (b : Basis ι (invariantRing G F B) (DB B ρ)) :
    ⇑(h.basisOfIsAdmissible ρ hadm b) = fun i => (b i : B ⊗[F] V) := by sorry
