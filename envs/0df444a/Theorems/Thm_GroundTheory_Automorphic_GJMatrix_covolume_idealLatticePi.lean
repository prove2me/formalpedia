-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_covolume_idealLatticePi
-- name    : GroundTheory.Automorphic.GJMatrix.covolume_idealLatticePi
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:56:13.77792+00:00
-- url     : https://prove2.me/theorems/13f4b957-dded-46fd-a78d-c098747b1095
-- title:
--   GJMatrix: covolume ideal Lattice Pi
-- statement:
--   The GJMatrix construction uses the covolume ideal Lattice Pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L244-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L244-L252

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
variable {K}

theorem GroundTheory.Automorphic.GJMatrix.covolume_idealLatticePi (I : ι → (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (idealLatticePi I) (mixedMeasurePi K) =
      ∏ i, ((FractionalIdeal.absNorm (I i : FractionalIdeal (𝓞 K)⁰ K) : ℝ) * √|(discr K : ℝ)|) := by sorry
