-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_prodExp_eq_expG_prodExpCoord
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.prodExp_eq_expG_prodExpCoord
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:32:59.651383+00:00
-- url     : https://prove2.me/theorems/246b1e89-7e15-4b0e-add6-735b5a6c0609
-- title:
--   Is Exp Lie Algebra: prod Exp eq exp G prod Exp Coord
-- statement:
--   The Is Exp Lie Algebra construction uses the prod Exp eq exp G prod Exp Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpHaar.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpHaar.lean#L17-L31

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarDensity
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open MeasureTheory Metric Set Filter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.prodExp_eq_expG_prodExpCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) {z : Fin d → ℝ}
    (hz : prodExpVal (fun i => (b i : 𝔸)) z ∈ h.nhdOne) :
    h.prodExp (⇑b) z = h.expG (b.equivFun.symm (prodExpCoord b z)) := by sorry
