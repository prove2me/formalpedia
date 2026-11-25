-- Prove2me | Theorems.Thm_GlobalTheory_Mass_PrimDisc_gens_swap
-- name    : GlobalTheory.Mass.PrimDisc.gens_swap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:38:36.523969+00:00
-- url     : https://prove2.me/theorems/7e79b0b3-ca03-5bde-8c2b-86bad96e5cd7
-- title:
--   Prim Disc: gens swap
-- statement:
--   The Prim Disc construction uses the gens swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveHermitianSublatticeDiscriminantGenerato.lean#L107-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveHermitianSublatticeDiscriminantGenerato.lean#L107-L148

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
omit [StarRing K] [FiniteDimensional K V] [NumberField K]

theorem GlobalTheory.Mass.PrimDisc.gens_swap (A B : Submodule K V) (p : V →ₗ[K] A) (q : V →ₗ[K] B)
    (hp : ∀ a : A, p a = a) (hpq : ∀ x, (p x : V) + q x = x) (L : Submodule (𝓞 K) V) (t : Finset B)
    (ht : L.map (q.restrictScalars (𝓞 K)) = latIn B L ⊔ Submodule.span (𝓞 K) (t : Set B)) :
    ∃ t' : Finset A, t'.card ≤ t.card ∧
      L.map (p.restrictScalars (𝓞 K)) = latIn A L ⊔ Submodule.span (𝓞 K) (t' : Set A) := by sorry
