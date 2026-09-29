-- Prove2me | Theorems.Thm_ModularCurve_mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero
-- name    : ModularCurve.mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/52d330b1-55da-5ad7-9a82-8564b8be0141
-- title:
--   Regular differentials spanned by restrictions of global 1-forms
-- statement:
--   Fix $N \ge 1$ and a prime $p$, and write $R = \mathbf{Z}_{(p)}$ for the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbf{Q}$ consisting of the rationals whose denominator is coprime to $p$. Let $X$ be an integral scheme with a morphism $c \colon X \to \operatorname{Spec} R$ that is proper and smooth of relative dimension $1$, and let $\mathcal{V}$ be a two-affine open cover of $X$: affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = X$ and $U_0 \cap U_1$ affine, giving $R$-algebras $A_0 = \Gamma(X, U_0)$, $A_1 = \Gamma(X, U_1)$, $A_{01} = \Gamma(X, U_0 \cap U_1)$ with the two restriction maps. Write $\bar{F}_N$ for `modularFunctionFieldBar N`, the base change to $\overline{\mathbf{Q}}$ inside $\mathrm{Laurent}(\overline{\mathbf{Q}})$ of the intermediate field $F_N = \mathbf{Q}(\text{divisorExpansions } N) \subseteq \mathrm{Laurent}(\mathbf{Q})$. Let $\iota \colon A_0 \to \bar{F}_N$ be a ring homomorphism such that $\iota \circ (R \to A_0)$ equals $R \to \overline{\mathbf{Q}} \to \bar{F}_N$, such that $\iota$ is injective, such that every $\iota(a)$ is the coefficientwise image `coeffEmb` of some element of $F_N$, and such that every $x \in F_N$ satisfies $\mathrm{coeffEmb}(x) \cdot \iota(b) = \iota(a)$ for some $a, b \in A_0$ with $\iota(b) \neq 0$. Let $H$ denote $(\mathcal{V}.\mathrm{kaehlerSections}\, c).H_0$, the kernel of the Čech differential on $\Omega_{A_0/R} \times \Omega_{A_1/R}$, and let $\mathrm{res} \colon H \to \Omega_{\bar{F}_N/\overline{\mathbf{Q}}}$ be an additive map that on each $\omega$ is the Kähler functoriality map [`KaehlerDifferential.mapOfRingHom`](def/AlgebraicGeometry_TwoAffineOpenCoverKaehler.html#L16) along $R \to \overline{\mathbf{Q}}$ and $\iota$ applied to the first component of $\omega$. Then every $\eta \in \Omega_{\bar{F}_N/\overline{\mathbf{Q}}}$ which is regular, in the sense that for each place $v$ of $\bar{F}_N$ over $\overline{\mathbf{Q}}$ one has $\eta = f \cdot \mathrm{d}(\text{uniformiser at } v)$ for some $f$ in the valuation subring of $v$, lies in the $\overline{\mathbf{Q}}$-span of the range of $\mathrm{res}$.
--
--   This is the surjectivity half, up to $\overline{\mathbf{Q}}$-scalars, of the comparison between the global $1$-forms of an integral proper smooth relative curve over $\mathbf{Z}_{(p)}$ and the regular differentials of $\overline{\mathbf{Q}} \cdot F_N$: combined with the inclusion in the other direction it identifies the $\overline{\mathbf{Q}}$-span of $\mathrm{res}(H)$ with $\Omega^{\mathrm{reg}}(\bar{F}_N/\overline{\mathbf{Q}})$, the semilinearity of $\mathrm{res}$ accounting for the span. It feeds the comparison of $q$-expansions of integral global $1$-forms on a rational curve model with those of the cusp sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open ModularCurve

theorem ModularCurve.mem_span_range_res_of_mem_regularDifferentialsBar_of_chartMap_of_neZero
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt p))) [IsIntegral X] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    (ι : (𝒱.cover c).A0 →+* ↥(modularFunctionFieldBar N))
    (hιR : ι.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (𝒱.cover c).A0) =
      (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))
    (hιinj : Function.Injective ι)
    (hιrat : ∀ a : (𝒱.cover c).A0, ∃ x ∈ modularFunctionFieldFull N,
      coeffEmb (AlgebraicClosure ℚ) x = (ι a : LaurentSeries (AlgebraicClosure ℚ)))
    (hιfrac : ∀ x ∈ modularFunctionFieldFull N, ∃ a b : (𝒱.cover c).A0, ι b ≠ 0 ∧
      coeffEmb (AlgebraicClosure ℚ) x * (ι b : LaurentSeries (AlgebraicClosure ℚ)) = ι a)
    (res : ↥((𝒱.kaehlerSections c).H0) →+ Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ])
    (hres : ∀ ω : ↥((𝒱.kaehlerSections c).H0),
      res ω = KaehlerDifferential.mapOfRingHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) ι hιR ω.val.1)
    (η : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) (hη : η ∈ regularDifferentialsBar N) :
    η ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range res) := by sorry
