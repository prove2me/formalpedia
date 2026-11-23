-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_hE_blockOne_cons
-- name    : GlobalTheory.CompanionTheory.SW.BlockAlg.hE_blockOne_cons
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:57.872031+00:00
-- url     : https://prove2.me/theorems/3ba2d777-1af6-4d79-8331-31f7f87a23fd
-- title:
--   Block Alg: h E block One cons
-- statement:
--   The Block Alg construction uses the h E block One cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L36-L42

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BlockAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.BlockAlg.hE_blockOne_cons (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t a b : E)
    (x y : Fin M → E) :
    hE σ (blockOne t J) (Fin.cons a x : Fin (M + 1) → E) (Fin.cons b y : Fin (M + 1) → E) =
      σ a * t * b + hE σ J x y := by sorry
