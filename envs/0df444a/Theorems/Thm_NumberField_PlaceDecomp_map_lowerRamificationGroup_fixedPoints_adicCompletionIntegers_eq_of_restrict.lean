-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict
-- name    : NumberField.PlaceDecomp.map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/31d51031-50e9-522f-bd45-e312064835ee
-- title:
--   Lower ramification groups of a quotient decomposition group
-- statement:
--   Let $E$, $L$, $F$ be number fields equipped with algebra structures $E\to L\to F$ forming a scalar tower, with $F/E$ Galois and $L/E$ normal. Let $w$ be a height-one prime of $\mathcal O_F$ and let $w.\mathrm{under}\,(\mathcal O_L)$ be the prime of $\mathcal O_L$ lying under it. Write $\mathrm{decomp}\,E\,F\,w$ for the decomposition subgroup of $F\simeq_{\mathrm{alg}[E]}F$, that is the stabiliser of the valuation subring of the $w$-adic valuation on $F$, and likewise $\mathrm{decomp}\,E\,L\,(w.\mathrm{under}\,(\mathcal O_L))$ inside $L\simeq_{\mathrm{alg}[E]}L$. Let $r$ be a monoid homomorphism from $\mathrm{decomp}\,E\,F\,w$ to $\mathrm{decomp}\,E\,L\,(w.\mathrm{under}\,(\mathcal O_L))$ which is surjective and which, for every $\sigma$ in the source, sends $\sigma$ to the automorphism of $L$ obtained from $\sigma$ by `AlgEquiv.restrictNormalHom L`. Let $i$ be a natural number. The assertion is an equality of subgroups of $\mathrm{decomp}\,E\,L\,(w.\mathrm{under}\,(\mathcal O_L))$: the image, under the monoid homomorphism underlying the isomorphism $\mathrm{decomp}\,E\,F\,w/\ker r\cong\mathrm{decomp}\,E\,L\,(w.\mathrm{under}\,(\mathcal O_L))$ induced by $r$, of the $i$-th lower ramification group of the quotient group $\mathrm{decomp}\,E\,F\,w/\ker r$ acting on the subring of $\ker r$-fixed points of the valuation ring $w.\mathrm{adicCompletionIntegers}\,F$ of the $w$-adic completion of $F$ — namely the inertia subgroup of the $(i+1)$-st power of the maximal ideal of that local ring, the elements acting trivially modulo $\mathfrak m^{i+1}$ — coincides with the $i$-th lower ramification group of $\mathrm{decomp}\,E\,L\,(w.\mathrm{under}\,(\mathcal O_L))$ acting on the valuation ring $(w.\mathrm{under}\,(\mathcal O_L)).\mathrm{adicCompletionIntegers}\,L$ of the completion of $L$ at the prime below $w$.
--
--   This is the compatibility of the lower ramification filtration with passage to a quotient of a decomposition group: on completions the fixed ring $\mathcal O_{F_w}^{\ker r}$ is identified with $\mathcal O_{L_{w_L}}$ equivariantly, so the two filtrations correspond under the isomorphism induced by restriction to $L$. It feeds the counting identity for cardinalities of lower ramification groups, the compatibility of the upper filtration with restriction, and the composition formula for the Herbrand function $\varphi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [Normal E L]
    (w : HeightOneSpectrum (𝓞 F))
    (r : ↥(NumberField.PlaceDecomp.decomp E F w) →* ↥(NumberField.PlaceDecomp.decomp E L (w.under (𝓞 L))))
    (hsurj : Function.Surjective r)
    (hr : ∀ σ : ↥(NumberField.PlaceDecomp.decomp E F w),
      ((r σ : ↥(NumberField.PlaceDecomp.decomp E L (w.under (𝓞 L)))) : L ≃ₐ[E] L) =
        AlgEquiv.restrictNormalHom L (σ : F ≃ₐ[E] F))
    (i : ℕ) :
    (IsLocalRing.lowerRamificationGroup
        ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥r.ker)
        (↥(NumberField.PlaceDecomp.decomp E F w) ⧸ r.ker) i).map
      (QuotientGroup.quotientKerEquivOfSurjective r hsurj).toMonoidHom =
    IsLocalRing.lowerRamificationGroup ↥((w.under (𝓞 L)).adicCompletionIntegers L)
      ↥(NumberField.PlaceDecomp.decomp E L (w.under (𝓞 L))) i := by sorry
