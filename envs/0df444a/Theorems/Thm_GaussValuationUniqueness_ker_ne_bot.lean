-- Prove2me | Theorems.Thm_GaussValuationUniqueness_ker_ne_bot
-- name    : GaussValuationUniqueness.ker_ne_bot
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:50:49.521196+00:00
-- url     : https://prove2.me/theorems/5c147c55-e440-44b9-817c-f60f7b0b9074
-- title:
--   Gauss Valuation Uniqueness: ker ne bot
-- statement:
--   The Gauss Valuation Uniqueness construction uses the ker ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/KerNeBot.lean#L10-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/KerNeBot.lean#L10-L55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_NotInjOfTrdeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_KerNeBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))

theorem GaussValuationUniqueness.ker_ne_bot (hv : IsTrivOn K v) (j0 : Fin (N + 1)) (a : Fin (N + 1) → Ω)
    (ha : ∀ j, a j ∈ vRing v) (hD : 1 ≤ D)
    (htr : letI := resAlg (F := K) v
      Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
        (IntermediateField.adjoin (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K Ω)))
          {r | ∃ j, ∃ h : a j ∈ vRing v, r = IsLocalRing.residue (vRing v) ⟨_, h⟩}) =
        ((D - 1 : ℕ) : Cardinal)) :
    RingHom.ker (psiR (D := D) v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) ≠ ⊥ := by sorry
