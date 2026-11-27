-- Prove2me | Theorems.Thm_GroundTheory_Global_idealLattice_poisson_summation
-- name    : GroundTheory.Global.idealLattice_poisson_summation
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:22.422161+00:00
-- url     : https://prove2.me/theorems/5ed800b7-c44c-4a41-9dfa-b32ed8e9dc34
-- title:
--   Global: ideal Lattice poisson summation
-- statement:
--   The Global construction uses the ideal Lattice poisson summation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticePoisson.lean#L25-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceLatticePoisson.lean#L25-L70

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticeEuclidean
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical RealInnerProductSpace FourierTransform SchwartzMap nonZeroDivisors
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.idealLattice_poisson_summation (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) (a : mixedSpace K) :
    ∑' α : idealLattice K I, f (α + a) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)|)⁻¹ •
        ∑' β : idealLattice K (traceDualIdeal K I),
          mixedFourier K f β * 𝐞 (mixedTraceForm K β a) := by sorry
