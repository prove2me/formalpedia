-- Prove2me | Theorems.Thm_NumberField_Idele_norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord
-- name    : NumberField.Idele.norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/734e59b8-5a02-5b4c-9aa2-600b8ea64fab
-- title:
--   Local norm of a principal idele as a power of ‖varpiᵥ‖
-- statement:
--   Let $K$ be a number field, let $v$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_K$, let $\varpi$ be an element of the valuation ring $\mathcal{O}_{K_v}$ of the $v$-adic completion $K_v$ which is irreducible in that ring, and let $u$ be a unit of $K$. Write $n$ for the integer $\mathrm{ord}_v$ attached to the principal idele of $u$, that is, the image of $u$ under the map of unit groups induced by the ring homomorphism $K \to \mathbb{A}_K$; by definition this integer is $-\mathrm{log}$ of the value, in the multiplicatively written value group $\mathbb{Z}^{\mathrm{WithZero}}$, of the $v$-adic valuation of the $v$-component of the finite part of that idele. The assertion is the equality of real numbers
--   $$\bigl\|\,\mathrm{algebraMap}_{K \to K_v}(u)\,\bigr\| = \bigl\|\varpi\bigr\|^{\,n},$$
--   the norms being those of the normed field structure on $K_v$ coming from its valuation, and the right-hand side being an integer power (possibly negative) of the norm of the image of $\varpi$ in $K_v$.
--
--   This is the standard comparison between the $v$-adic absolute value of an element of $K^\times$ and its valuation read off from the finite part of the associated principal idele, with the absolute value normalised by an arbitrary uniformiser of $\mathcal{O}_{K_v}$. It serves as bookkeeping between local absolute values and the idelic valuation profile, and is used in the computations of orbital and window integrals for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord.lean

import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.Idele.norm_algebraMap_adicCompletion_eq_norm_uniformizer_zpow_ord
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (u : Kˣ) :
    ‖algebraMap K (v.adicCompletion K) (u : K)‖ =
      ‖(ϖ : v.adicCompletion K)‖ ^
        NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) := by sorry
