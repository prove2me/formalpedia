-- Prove2me | Theorems.Thm_GlobalTheory_AbCoh_SplitCx_exists_quasiInv
-- name    : GlobalTheory.AbCoh.SplitCx.exists_quasiInv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:12:35.497613+00:00
-- url     : https://prove2.me/theorems/0a7c08d5-892b-52ad-969c-d8877fdd3cd8
-- title:
--   Split Cx: exists quasi Inv
-- statement:
--   The Split Cx construction uses the exists quasi Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CohomSplitBaseChange.lean#L17-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CohomSplitBaseChange.lean#L17-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CohomSplitBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.SplitCx
variable {R : Type} [CommRing R]

theorem GlobalTheory.AbCoh.SplitCx.exists_quasiInv {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R N] (d : M →ₗ[R] N) (hQ : Module.Projective R (N ⧸ LinearMap.range d)) :
    ∃ b : N →ₗ[R] M, ∀ x, d (b (d x)) = d x := by sorry
