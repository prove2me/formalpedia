-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_mem_fixedGrading
-- name    : GlobalTheory.GaloisDescent.mem_fixedGrading
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:29.680074+00:00
-- url     : https://prove2.me/theorems/b9a8845a-e2ae-4b0e-9ed9-4aa175f0ad99
-- title:
--   Galois Descent: mem fixed Grading
-- statement:
--   The Galois Descent construction uses the mem fixed Grading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueHomogeneousIdealFixedSubalgebra.lean#L233-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueHomogeneousIdealFixedSubalgebra.lean#L233-L234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueHomogeneousIdealFixedSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L G A : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
  [Ring A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
  [MulSemiringAction G A] [SMulDistribClass G L A] [SMulCommClass G K A]
variable {ι : Type*} (𝒜 : ι → Submodule L A)
omit [MulSemiringAction G L] [SMulDistribClass G L A]

theorem GlobalTheory.GaloisDescent.mem_fixedGrading {i : ι} {a : FixedPoints.subalgebra K A G} :
    a ∈ fixedGrading K G 𝒜 i ↔ (a : A) ∈ 𝒜 i := by sorry
