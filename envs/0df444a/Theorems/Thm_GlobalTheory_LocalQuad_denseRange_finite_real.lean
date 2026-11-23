-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_denseRange_finite_real
-- name    : GlobalTheory.LocalQuad.denseRange_finite_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:41.015802+00:00
-- url     : https://prove2.me/theorems/c7a97824-cd6e-4f6d-8293-375bb1b51917
-- title:
--   Local Quad: dense Range finite real
-- statement:
--   The Local Quad construction uses the dense Range finite real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsForallAbvSubLt.lean#L106-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsForallAbvSubLt.lean#L106-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open NumberField IsDedekindDomain
open scoped Matrix WithZero
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.LocalQuad.denseRange_finite_real (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    DenseRange (fun x : F =>
      ((fun v : T => algebraMap F (v.1.adicCompletion F) x, fun σ : F →+* ℝ => σ x) :
        ((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ))) := by sorry
