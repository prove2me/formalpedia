-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_herm_diagonal_self
-- name    : GlobalTheory.UTrans.herm_diagonal_self
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:54:34.690703+00:00
-- url     : https://prove2.me/theorems/9715a8e4-5907-4b77-a8b3-0c40b3e81430
-- title:
--   UTrans: herm diagonal self
-- statement:
--   The UTrans construction uses the herm diagonal self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicOfIndefinite.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicOfIndefinite.lean#L21-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__LandherrStIffLandherr_9fec213082f17e18
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicOfIndefinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.UTrans
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.UTrans.herm_diagonal_self {r : ℕ} (g u : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal g) u u = ∑ i, u i * g i * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (u i) := by sorry
