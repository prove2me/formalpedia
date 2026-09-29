-- Prove2me | Theorems.Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
-- name    : ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/34f8252f-1e6b-5688-b7be-ba2b99bb3770
-- title:
--   Frobenius permutes the supersingular q-expansion places
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $p$, with $p$ a prime, and let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$. Let $\bar F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) be the intermediate field of the Laurent series field $K((q))$ obtained by adjoining to $K$ the set `intFormRatiosC K Γ`, and let [`ModularCurve.qExpFrobeniusModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L76) be the $K$-algebra endomorphism of $\bar F$ induced by the substitution $q \mapsto q^{p}$ on Laurent series; since this endomorphism is integral, each place $w$ of $\bar F$ over $K$ (a valuation subring of $\bar F$ containing the image of $K$, proper, and a principal ideal ring) may be restricted along it, giving the place [`ModularCurve.qExpFrobeniusPlaceModL K Γ p w`](def/ModularCurve_QExpFrobeniusModL.html#L132). Let [`ModularCurve.ssPlacesQExp K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L27) be the set of those places $v$ for which there exist $x \in \bar F$ whose Laurent series is `jqModC K` and $a \in K$ such that $x$ lies in the valuation ring of $v$ with residue $a$, and $a$ belongs to the subset [`ModularCurve.ssJSet p K`](def/ModularCurve_SupersingularModuli.html#L7) of $K$. The assertion is that the image of this set of places under [`ModularCurve.qExpFrobeniusPlaceModL K Γ p`](def/ModularCurve_QExpFrobeniusModL.html#L132) is exactly that same set.
--
--   This records that the Frobenius operation on places of the $q$-expansion function field of $X(\Gamma)$ in characteristic $p$ permutes the supersingular places, i.e. those places at which the reduced $j$-expansion is regular with value in the designated supersingular set. It is used in the treatment of regular differentials and of the Néron-model data at $p$ on the modular curves $X_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.image_qExpFrobeniusPlaceModL_ssPlacesQExp_eq
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ModularCurve.qExpFrobeniusPlaceModL K Γ p '' ModularCurve.ssPlacesQExp K Γ p =
      ModularCurve.ssPlacesQExp K Γ p := by sorry
