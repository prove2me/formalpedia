-- Prove2me | Theorems.Thm_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull
-- name    : ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/f437bb30-7626-5a48-a475-a97a35f44320
-- title:
--   Integral q-expansions at the cusp ∞ from a retraction
-- statement:
--   Let $R$ and $R'$ be commutative rings with $R$ carrying a $\mathbb{Q}$-algebra structure, and let $p$ be a nonzero natural number. Let $M$ be a curve model over $\mathbb{Q}$ of the field $F_p := \mathbb{Q}(\,\mathrm{qExpand}\,\mathbb{Q}\,d\,\mathrm{jq} : d \mid p\,) \subseteq \mathbb{Q}((q))$, that is: an integral scheme $M.C$ proper and smooth of relative dimension $1$ over $\operatorname{Spec}\mathbb{Q}$, a ring isomorphism $M.\mathrm{ffEquiv} : F_p \to$ the function field of $M.C$ compatible with the structure map on $\mathbb{Q}$, and a bijection $M.\mathrm{placeOfPoint}$ from closed points of $M.C$ to places of $F_p$ over $\mathbb{Q}$ (proper valuation subrings containing $\mathbb{Q}$ whose ideals are principal) such that the image of the stalk at a closed point inside $F_p$ is exactly the corresponding valuation subring. Let $x$ be a closed point with $M.\mathrm{placeOfPoint}\,x = \mathrm{cuspInftyFull}\,p$, the place whose valuation subring is that of the $q$-adic valuation on $F_p$ (normalised by $\operatorname{ord}(\mathrm{jq}) = -1$). For $g$ in the stalk $\mathcal{O}_{M.C,x}$ write $\widehat g \in \mathbb{Q}((q))$ for the Laurent series obtained by mapping $g$ to the function field and transporting it by $M.\mathrm{ffEquiv}^{-1}$ into $F_p \subseteq \mathbb{Q}((q))$. Assume given ring homomorphisms $\iota : R \to R'$ and $\pi : R' \to R$ with $\pi \circ \iota = \mathrm{id}_R$, an element $t \in R'$ with $\pi t = 0$ such that $\ker\pi \subseteq (t) + (\ker\pi)^2$, and a ring homomorphism $\mathrm{route} : R' \to \mathcal{O}_{M.C,x}$ satisfying: $\widehat{\mathrm{route}(\iota r)}$ is the constant series with value the image of $r$ in $\mathbb{Q}$, for all $r \in R$; $\mathrm{route}(\ker\pi)$ lies in the maximal ideal of $\mathcal{O}_{M.C,x}$; and $\widehat{\mathrm{route}(t)}$ is the Laurent series of the image of some $u \in R[[q]]$ under $R \to \mathbb{Q}$. Then for every $z \in R'$ there is $P \in R[[q]]$ such that $\widehat{\mathrm{route}(z)}$ is the Laurent series attached to the image of $P$ under $R \to \mathbb{Q}$, and the constant coefficient of $P$ is $\pi z$.
--
--   This is the weight-zero $q$-expansion principle at the cusp $\infty$ in the vocabulary of curve models and $q$-adic places: a function arising from $R'$ via $\mathrm{route}$ has $q$-expansion with no pole, coefficients in $R$, and constant term equal to its value along the retraction $\pi$. It combines the statement that expansions of germs at the cusp point have nonnegative order and that germs in the maximal ideal have vanishing constant coefficient with the purely ring-theoretic result [`RingHom.exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq`](thm.html#RingHom.exists_powerSeries_map_eq_and_constantCoeff_eq_of_retraction_of_ker_le_span_sup_sq), and is used in the form of the statement for the cusp section of an integral model, [`ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero`](thm.html#ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_stalkMap_stalkSpecializes_cuspSection_of_ratCurveModel_compat_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.lean

import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry

theorem ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R ℚ]
    (p : ℕ) [NeZero p]
    (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
    (x : closedPoints M.C) (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    (ι : R →+* R') (π : R' →+* R) (hπ : π.comp ι = RingHom.id R)
    (t : R') (ht : π t = 0) (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2)
    (route : R' →+* M.C.presheaf.stalk x.1)
    (hι : ∀ r : R, ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route (ι r))) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) = HahnSeries.C (algebraMap R ℚ r))
    (hI : ∀ i ∈ RingHom.ker π, route i ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1))
    (u : PowerSeries R)
    (hu : ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route t)) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) =
      HahnSeries.ofPowerSeries ℤ ℚ (u.map (algebraMap R ℚ)))
    (z : R') :
    ∃ P : PowerSeries R,
      ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route z)) :
          ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) =
        HahnSeries.ofPowerSeries ℤ ℚ (P.map (algebraMap R ℚ)) ∧
      PowerSeries.constantCoeff P = π z := by sorry
