-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi
-- name    : NumberField.PlaceDecomp.valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8a89a8ee-4cda-59fc-b42d-5c7eb8ad4871
-- title:
--   Transitivity of the Herbrand function in a tower of number fields
-- statement:
--   Let $E$, $L$, $F$ be number fields with algebra structures $E \to L \to F$ forming a scalar tower, $F/E$ Galois and $L/E$ normal, let $w$ be a height-one prime of the ring of integers $\mathcal{O}_F$, and let $u$ be a rational number with $0 \le u$. For a number field $K'$ with subfield $K$ and a valuation subring $A \subseteq K'$, the quantity [`ValuationSubring.herbrandPhi`](def/Mathlib_RingTheory_Valuation_UpperRamificationGroup.html#L255) is the Herbrand function of the group $G$ of $K$-algebra automorphisms of $K'$ stabilising $A$ acting on $A$: it equals $u$ for $u \le 0$, and otherwise $$\Bigl(\sum_{i=1}^{\lfloor u \rfloor} \#G_i + (u - \lfloor u \rfloor)\,\#G_{\lfloor u \rfloor + 1}\Bigr) \big/ \#G_0,$$ where $G_i$ denotes the $i$-th lower ramification group of the action and $\#$ the cardinality. The assertion is that the Herbrand function over $E$ of the valuation subring of $F$ cut out by the $w$-adic valuation, evaluated at $u$, coincides with the Herbrand function over $E$ of the valuation subring of $L$ cut out by the valuation of the prime $w \cap \mathcal{O}_L$ below $w$, evaluated at the value at $u$ of the Herbrand function over $L$ of the valuation subring of $F$ at $w$.
--
--   This is the transitivity (composition) formula $\varphi_{F_w/E_v} = \varphi_{L_{w_L}/E_v} \circ \varphi_{F_w/L_{w_L}}$ for Herbrand's function attached to a tower of number fields at a finite place, in the form obtained from Herbrand's theorem on the image of the lower ramification filtration under passage to a quotient decomposition group. It feeds the construction of the upper ramification filtration for places of number fields, being used in the statement on upper ramification groups and products over the quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [Normal E L]
    (w : HeightOneSpectrum (𝓞 F)) (u : ℚ) (hu : 0 ≤ u) :
    ValuationSubring.herbrandPhi E ((w.valuation F).valuationSubring) u =
      ValuationSubring.herbrandPhi E (((w.under (𝓞 L)).valuation L).valuationSubring)
        (ValuationSubring.herbrandPhi L ((w.valuation F).valuationSubring) u) := by sorry
