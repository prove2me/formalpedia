-- Prove2me | Theorems.Thm_GaussValuationUniqueness_pos_of_ker
-- name    : GaussValuationUniqueness.pos_of_ker
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:50:50.524696+00:00
-- url     : https://prove2.me/theorems/27fc7796-a03e-46ee-ab00-4b4ea5e8f3c7
-- title:
--   Gauss Valuation Uniqueness: pos of ker
-- statement:
--   The Gauss Valuation Uniqueness construction uses the pos of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ImgRSuccAbove.lean#L61-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessLemmas/KernelLineArguments/ImgRSuccAbove.lean#L61-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
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

theorem GaussValuationUniqueness.pos_of_ker {w : AddValuation (OmS Ω D N) (WithTop ℤ)}
    (hw : ∀ a : Ω, w (algebraMap Ω (OmS Ω D N) a) = v a)
    (e : SVar D N → OmS Ω D N) (he : ∀ s, 0 ≤ w (e s))
    (q : MvPolynomial (SVar D N) (vRing v))
    (hq : MvPolynomial.map (IsLocalRing.residue (vRing v)) q = 0) :
    0 < w (MvPolynomial.eval₂ ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype) e q) := by sorry
