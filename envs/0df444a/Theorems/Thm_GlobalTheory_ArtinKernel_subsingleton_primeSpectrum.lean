-- Prove2me | Theorems.Thm_GlobalTheory_ArtinKernel_subsingleton_primeSpectrum
-- name    : GlobalTheory.ArtinKernel.subsingleton_primeSpectrum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:08.724332+00:00
-- url     : https://prove2.me/theorems/09648707-cebe-43e4-bf80-b491ba93bff7
-- title:
--   Artin Kernel: subsingleton prime Spectrum
-- statement:
--   The Artin Kernel construction uses the subsingleton prime Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfMulPeriod.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfMulPeriod.lean#L113-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.ArtinKernel
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]

theorem GlobalTheory.ArtinKernel.subsingleton_primeSpectrum : Subsingleton (PrimeSpectrum R) := by sorry
