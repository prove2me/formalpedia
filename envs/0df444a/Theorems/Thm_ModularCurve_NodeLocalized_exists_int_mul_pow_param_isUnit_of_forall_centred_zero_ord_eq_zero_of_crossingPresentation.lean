-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_zero_ord_eq_zero_of_crossingPresentation
-- name    : ModularCurve.NodeLocalized.exists_int_mul_pow_param_isUnit_of_forall_centred_zero_ord_eq_zero_of_crossingPresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/e925fefd-866f-58be-bdbd-29825e32b7e5
-- title:
--   Unit normalisation at the width-three supersingular node j=0
-- statement:
--   Fix a prime $q\ge 5$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$, and a ring homomorphism $\mathrm{red}:A\to k$ with $\mathrm{red}\,c=0$ exactly for $c$ in the maximal ideal of $A$; assume $0\in$ `ssJSet q k`, i.e. every elliptic curve over $k$ with $j$-invariant $0$ has no nonzero affine point killed by $q$. Let $K/\mathbb Q$ be a finite subextension of $\overline{\mathbb Q}$, $A_K=A\cap K$, and let $\varpi\in A_K$ satisfy $\mathrm{red}\,c=0\iff \varpi\mid c$ for $c\in A_K$, with $q=\varpi^{e_K}\varepsilon$, $\varepsilon$ a unit and $e_K\ge 1$. Let $R$ be the subring of Laurent series over $\overline{\mathbb Q}$ consisting of those $f$ with $f\cdot s(j,j_q)=r(j,j_q)$ for some $r,s\in A_K[X_0,X_1]$ whose $s$ has nonzero value at the point $(0,0^q)$ after reduction, where $j,j_q$ are the expansions used at level $1\cdot q$, and write $\pi\in R$ for the image of the constant $\varpi$. Given $G',H',w\in R$ with $w$ a unit, $G'H'=\pi^{\,\mathrm{jWidth}(0)\cdot e_K}w$ (so the exponent is $3e_K$, since `jWidth` takes the value $3$ at $0$), the maximal ideal of $R$ equal to $(\pi,G',H')$, the ideals $(\pi,G')$ and $(\pi,H')$ prime with $H'\notin(\pi,G')$ and $G'\notin(\pi,H')$, and $(\pi,G')=(\pi,\,(X_1-X_0^q)(j,j_q))$, $(\pi,H')=(\pi,\,(X_0-X_1^q)(j,j_q))$: then for every $Gf$ in $\overline{\mathbb Q}\cdot$`modularFunctionFieldFull (1*q)` whose underlying Laurent series is that of $G'$, and every nonzero $f$ in that field such that $W.\mathrm{ord}\,f=0$ for all places $W$ of it over $\overline{\mathbb Q}$ centred at the node — those for which there are $x,y\in A$ with $\mathrm{red}\,x=0$, $\mathrm{red}\,y=0^q$ and $W.\mathrm{ord}(j-x)>0$, $W.\mathrm{ord}(j_q-y)>0$ — there exist $m\in\mathbb Z$ and $c\in\overline{\mathbb Q}$, $c\ne 0$, such that at every such centred place $W$ the element $W.\mathrm{evalAt}(f)\,c^{-1}\,(W.\mathrm{evalAt}\,Gf)^{-m}$ lies in $A$ and is a unit there.
--
--   This is the unit principle on the tube around the supersingular node $j=0$ of $X_0(q)$, whose width in the Deligne–Rapoport model is three: from a crossing presentation $G'H'=\pi^{3e_K}w$ of the local ring at the node it extracts, for any function with order zero at all places centred at the node, a slope $m$ and a leading constant $c$ normalising it to a unit at each such place. It feeds the construction of the supersingular annulus at $j=0$ in [`ModularCurve.exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes`](thm.html#ModularCurve.exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_zero_ord_eq_zero_of_crossingPresentation.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.exists_int_mul_pow_param_isUnit_of_forall_centred_zero_ord_eq_zero_of_crossingPresentation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (ha : (0 : k) ∈ ssJSet q k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))) ^ (jWidth (0 : k) * eK) * w)
    (hmax : ∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))],
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)) =
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G', H'})
    (heK1 : 1 ≤ eK)
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G'}).IsPrime)
    (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G'})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))}) :
∀ Gf : ↥(modularFunctionFieldBar (1 * q)),
      (Gf : LaurentSeries (AlgebraicClosure ℚ)) = (G' : LaurentSeries (AlgebraicClosure ℚ)) →
        ∀ f : ↥(modularFunctionFieldBar (1 * q)), f ≠ 0 →
          (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
            ((∃ x : A, red x = (0 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (0 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0) →
          ∃ (m : ℤ) (c : AlgebraicClosure ℚ), c ≠ 0 ∧
            ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
              ((∃ x : A, red x = (0 : k) ∧
              0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
              (∃ y : A, red y = (0 : k) ^ q ∧
              0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
                ∃ h : W.evalAt f * c⁻¹ * (W.evalAt Gf) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A) := by sorry
