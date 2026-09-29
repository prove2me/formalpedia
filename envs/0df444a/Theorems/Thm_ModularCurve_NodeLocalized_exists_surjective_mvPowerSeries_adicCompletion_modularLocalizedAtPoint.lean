-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_surjective_mvPowerSeries_adicCompletion_modularLocalizedAtPoint
-- name    : ModularCurve.NodeLocalized.exists_surjective_mvPowerSeries_adicCompletion_modularLocalizedAtPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/ad745115-fe08-5192-9bbb-8a35f7542400
-- title:
--   Surjection from W[[X₀,X₁]] onto the completed node ring
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $k$ be a field of characteristic $q$, let $\mathrm{red}\colon A \to k$ be a ring homomorphism and $a \in k$, and let $K$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ with $K$ finite over $\mathbb Q$. Write $A_0 := A \cap K$ for the subring `coeffSubring A K` of $\overline{\mathbb Q}$ and $\mathrm{red}_0\colon A_0 \to k$ for the restriction of $\mathrm{red}$. Assume given $x \in A_0$ with $\mathrm{red}_0(x) = a$, and $\varpi \in A_0$ such that for every $c \in A_0$ one has $\mathrm{red}_0(c) = 0$ if and only if $\varpi \mid c$; assume also that the ring $R_0 :=$ `modularLocalizedAtPoint (1 * q)` $A_0\,\mathrm{red}_0\,a\,(a^q)$ is local. Here $R_0$ is the subring of Laurent series over $\overline{\mathbb Q}$ consisting of those $f$ for which there are two-variable polynomials $r, s$ over $A_0$ with $s(a, a^q) \neq 0$ (evaluated through $\mathrm{red}_0$) and $f \cdot s(j, j_{1\cdot q}) = r(j, j_{1\cdot q})$, where $j$ is the $q$-expansion `jqModC` of $j$ and $j_{1\cdot q}$ is its substitution `jqNModC` at level $1\cdot q$. Put $W := \mathrm{PowerSeries}\,A_0 / (X - C(\varpi))$ and let $\widehat{R_0}$ be the adic completion of $R_0$ at its maximal ideal. Then there exist ring homomorphisms $\theta_W\colon W \to \widehat{R_0}$ and $\theta\colon W[[X_0, X_1]] \to \widehat{R_0}$ (two-variable power series over $W$, indexed by `Fin 2`) such that: $\theta_W$ sends the class of the constant $C(o)$, for $o \in A_0$, to the image in $\widehat{R_0}$ of the constant Laurent series $o \in R_0$, and the class of $X$ to the image of $\varpi$; $\theta$ is surjective; $\theta$ composed after the constant inclusion $W \to W[[X_0, X_1]]$ equals $\theta_W$; and $\theta(X_0)$, $\theta(X_1)$ are the images in $\widehat{R_0}$ of $j - x$ and of $j_{1\cdot q} - x^q$ respectively.
--
--   This is the presentation of the completed local ring of the plane model of $X_0(q)$ at the point $(a, a^q)$ of its characteristic-$q$ fibre as a quotient of a two-variable power series ring over the complete discrete valuation ring $W = A_0[[t]]/(t - \varpi)$, a concrete model for the completion of $A_0$. It feeds the identification of that completed local ring with the crossing model $W[[u,v]]/(uv - \text{unit})$ used at the nodes of $X_0(q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_surjective_mvPowerSeries_adicCompletion_modularLocalizedAtPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.exists_surjective_mvPowerSeries_adicCompletion_modularLocalizedAtPoint
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))] :
    ∃ (θW : (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) →+* AdicCompletion (IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
      (θ : MvPowerSeries (Fin 2) (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) →+* AdicCompletion (IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))),
      (∀ o : ↥(coeffSubring A K), θW (Ideal.Quotient.mk _ (PowerSeries.C o))
          = algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) _ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C o),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))) ∧
      θW (Ideal.Quotient.mk _ PowerSeries.X) = algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) _ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∧
      Function.Surjective θ ∧
      θ.comp MvPowerSeries.C = θW ∧
      θ (MvPowerSeries.X 0) = algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) _ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C x),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∧
      θ (MvPowerSeries.X 1) = algebraMap ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) _ (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by sorry
