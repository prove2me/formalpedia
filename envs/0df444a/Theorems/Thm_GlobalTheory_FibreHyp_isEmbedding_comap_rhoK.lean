-- Prove2me | Theorems.Thm_GlobalTheory_FibreHyp_isEmbedding_comap_rhoK
-- name    : GlobalTheory.FibreHyp.isEmbedding_comap_rhoK
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:40.410589+00:00
-- url     : https://prove2.me/theorems/f44b3608-59cb-44e4-a411-53c86a1fc95e
-- title:
--   Fibre Hyp: is Embedding comap rho K
-- statement:
--   The Fibre Hyp construction uses the is Embedding comap rho K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean#L122-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.FibreHyp
variable {A : Type} [CommRing A] {σ : Type} (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k]

theorem GlobalTheory.FibreHyp.isEmbedding_comap_rhoK : Topology.IsEmbedding (PrimeSpectrum.comap (rhoK f g k).toRingHom) := by sorry
