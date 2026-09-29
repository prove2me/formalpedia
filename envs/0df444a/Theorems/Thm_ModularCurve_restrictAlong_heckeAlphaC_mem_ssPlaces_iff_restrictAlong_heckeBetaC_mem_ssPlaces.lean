-- Prove2me | Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces
-- name    : ModularCurve.restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/6adc3eb4-681f-5671-b858-cbff65d05cb0
-- title:
--   Supersingularity along the two legs of the ℓ-roof
-- statement:
--   Let $p$ be a prime, let $K$ be an algebraically closed field of characteristic $p$, let $N \ge 1$ and let $\ell$ be a prime with $(N : K) \ne 0$ (equivalently $p \nmid N$), $\ell \nmid N$ and $\ell \ne p$. Inside the Laurent series field $K((q))$ consider the level-$N$ modular function field $\mathtt{modularFunctionFieldC}\ K\ N = K(j(q), j(q^N))$ and the $\ell$-roof $\mathtt{charLDegeneracyRoof}\ K\ N\ \ell = K(j(q), j(q^N), j(q^{\ell}), j(q^{N\ell}))$, together with its two legs: $\mathtt{heckeAlphaC}$, the inclusion of the level-$N$ field into the roof, and $\mathtt{heckeBetaC}$, the map induced by the substitution $q \mapsto q^{\ell}$ on Laurent series. Both legs are assumed to be integral as ring homomorphisms. Let $y$ be a place of the roof over $K$, i.e. a valuation subring, different from the whole field, containing the image of $K$ and whose local ring is a principal ideal ring. Then the restriction of $y$ along $\alpha$ (the contraction of its valuation subring) is supersingular — rational, an affine geometric place, and with $j$-value in $\mathtt{ssJSet}\ p\ K$ — if and only if the restriction of $y$ along $\beta$ is.
--
--   This is the statement that the two degeneracy maps $X_0(N\ell) \to X_0(N)$, read on function fields as the inclusion and the $q \mapsto q^\ell$ leg of the $\ell$-roof, both preserve and both reflect supersingularity of places: an $\ell$-isogeny partner of a supersingular curve is supersingular in either direction. It is used in the construction and analysis of the supersingular Hecke operator, a trace along $\alpha$ of a pull-back along $\beta$, ensuring that operator sees only supersingular data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hN : (N : K) ≠ 0) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (y : Place K ↥(charLDegeneracyRoof K N ℓ)) :
    y.restrictAlong (heckeAlphaC K N ℓ) hα ∈ ssPlaces p N K ↔ y.restrictAlong (heckeBetaC K N ℓ) hβ ∈ ssPlaces p N K := by sorry
