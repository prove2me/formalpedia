-- Prove2me | Theorems.Thm_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero
-- name    : ModularCurve.kaehlerH0_res_injective_of_injective_chartMap_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/1024bd5a-df1e-53ac-8b52-1c515428e407
-- title:
--   Global differentials injected into Ω_̄ F_N/ℚ̄
-- statement:
--   Fix $N \ge 1$ and a prime $p$, and write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of $\mathbf Q$ consisting of those rationals whose denominator is coprime to $p$. Let $X$ be an integral scheme over $\operatorname{Spec} R$ via a morphism $c$ that is proper and smooth of relative dimension $1$, and let $\mathcal V$ be a `TwoAffineOpenCover` of $X$: affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \cap U_1$ affine. Write $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$, $A_{01} = \Gamma(X, U_0 \cap U_1)$, each an $R$-algebra through $c$. Let $\iota : A_0 \to$ `modularFunctionFieldBar N` be an injective ring homomorphism into the intermediate field between $\overline{\mathbf Q}$ and the Laurent series field $\overline{\mathbf Q}((X))$ obtained by base change to $\overline{\mathbf Q}$ of the full modular function field of level $N$, and assume $\iota$ is compatible with the structure maps, in the sense that $\iota \circ (R \to A_0)$ equals $R \to \overline{\mathbf Q} \to$ `modularFunctionFieldBar N`. Let $H^0$ denote the $R$-submodule of $\Omega_{A_0/R} \times \Omega_{A_1/R}$ cut out as the kernel of the Čech differential into $\Omega_{A_{01}/R}$, and let $\mathrm{res} : H^0 \to \Omega_{\mathrm{modularFunctionFieldBar}\,N/\overline{\mathbf Q}}$ be an additive map which on every $\omega$ is given by applying [`KaehlerDifferential.mapOfRingHom`](def/AlgebraicGeometry_TwoAffineOpenCoverKaehler.html#L16) for the pair $(R \to \overline{\mathbf Q}, \iota)$ to the first component of $\omega$. Then $\mathrm{res}$ is injective.
--
--   This says that a global relative $1$-form on an integral proper smooth curve over $\mathbf Z_{(p)}$, presented as a Čech $0$-cocycle for a two-chart affine cover, is determined by the image of its $U_0$-component in the differentials of the geometric modular function field; the proof cites formal smoothness of $\Gamma(X,U_0)$ over $R$. It feeds the level-$N$ integral $q$-expansion comparison [`ModularCurve.exists_linearEquiv_kaehlerH0_baseChange_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero`](thm.html#ModularCurve.exists_linearEquiv_kaehlerH0_baseChange_intLattice_of_ratCurveModel_of_cuspSection_compat_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_kaehlerH0_res_injective_of_injective_chartMap_of_neZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve

theorem ModularCurve.kaehlerH0_res_injective_of_injective_chartMap_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (hιinj : Function.Injective ι)
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1) :
    Function.Injective res := by sorry
