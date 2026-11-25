-- Prove2me | Theorems.Thm_GlobalTheory_Mass_PrimDisc_dual_latIn
-- name    : GlobalTheory.Mass.PrimDisc.dual_latIn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:40:07.951897+00:00
-- url     : https://prove2.me/theorems/6660fc26-7521-4cee-9122-d66899df0af9
-- title:
--   Prim Disc: dual lat In
-- statement:
--   The Prim Disc construction uses the dual lat In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveHermitianSublatticeDiscriminantGenerato.lean#L49-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveHermitianSublatticeDiscriminantGenerato.lean#L49-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveHermitianSublatticeDiscriminantGenerato
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimDisc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.Mass.PrimDisc.dual_latIn (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hp : PD h) (A : Submodule K V)
    (hsA : (hRes h A).IsSymm) (hpA : PD (hRes h A)) (p : V →ₗ[K] A) (hsur : Function.Surjective p)
    (hh : ∀ (x : V) (a : A), h (p x : V) (a : V) = h x a)
    (L : Submodule (𝓞 K) V) (hL : IsIntLat h L) :
    IsIntLat (hRes h A) (latIn A L) ∧
      dual (hRes h A) (latIn A L) = (dual h L).map (p.restrictScalars (𝓞 K)) := by sorry
