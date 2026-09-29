-- Prove2me | Theorems.Thm_ModularCurve_exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes
-- name    : ModularCurve.exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/8f25dd90-8b09-59f8-890a-6d744e5df187
-- title:
--   Width-three annulus at the supersingular crossing j=0
-- statement:
--   Fix a prime $q\ge 5$, a valuation subring $A$ of $\overline{\mathbb Q}$, and an algebraically closed field $k$ of characteristic $q$, together with a ring homomorphism $\mathrm{red}\colon A\to k$ whose zero set is exactly the maximal ideal of $A$; assume $0$ lies in `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $0$ has no nonzero point killed by $q$. Let $K\subset\overline{\mathbb Q}$ be a finite extension of $\mathbb Q$, put $R=A\cap K$ (`coeffSubring`), and let $\varpi\in R$ generate the kernel of the restriction of $\mathrm{red}$ to $R$, with $q=\varpi^{e_K}\varepsilon$ for a unit $\varepsilon\in R$ and $e_K\ge 1$. Work in the subring `modularLocalizedAtPoint` of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ consisting of series $f$ with $f\cdot\mathrm{modularEval}(s)=\mathrm{modularEval}(r)$ for two‑variable polynomials $r,s$ over $R$ with $s$ not vanishing at the point $(0,0^q)$, where `modularEval` sends $X_0,X_1$ to the reductions of the $q$-expansions $j$ and $j(q\tau)$; write $\pi$ for the image of the constant $\varpi$. Let $G',H',w$ lie in this ring with $w$ a unit, $G'H'=\pi^{\,3e_K}w$ (the exponent being `jWidth 0`$\cdot e_K$), with, whenever the ring is local, maximal ideal $(\pi,G',H')$, with $(\pi,G')$ and $(\pi,H')$ prime, $H'\notin(\pi,G')$, $G'\notin(\pi,H')$, and $(\pi,G')=(\pi,\,X_1-X_0^q)$, $(\pi,H')=(\pi,\,X_0-X_1^q)$ after `modularEval`. Then there are two annuli $An,An'$ over $A$ in `modularFunctionFieldBar` of level $q$ — each consisting of a set of places, a parameter and a modulus in the maximal ideal of $A$, subject to the axioms of `Annulus` — with the same domain and the same modulus, the modulus nonzero, and $An'.\mathrm{param}\cdot An.\mathrm{param}$ equal to the image of that modulus; the common domain consists exactly of those places $W$ for which there are $x,y\in A$ with $\mathrm{red}\,x=0$, $\mathrm{red}\,y=0^q$ and $W.\mathrm{ord}(j-x)>0$, $W.\mathrm{ord}(j(q\tau)-y)>0$; the parameter of $An$ is $G'$ as a Laurent series; and $An.\mathrm{modulus}=q^3$.
--
--   This supplies the semistable annulus chart at a supersingular crossing of the reduction of $X_0(q)$ lying over $j=0$, the modulus $q^3$ recording that such a crossing has width three, in accordance with the Deligne–Rapoport model. It is used by the place-specialisation and prolongation machinery, which assembles component charts and crossing exponents from crossing presentations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes.lean

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

open AlgebraicCurve ModularCurve
open ModularCurve.NodeLocalized

theorem ModularCurve.exists_ssAnnulus_centred_zero_of_crossingPresentation_of_branchPrimes
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
    ∃ (An An' : Annulus A ↥(modularFunctionFieldBar (1 * q))),
      (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
        ((An.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
        An'.param * An.param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
              ((An.modulus : AlgebraicClosure ℚ))) ∧
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        W ∈ An.dom ↔
          ((∃ x : A, red x = (0 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = (0 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) ∧
      ((An.param : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = (G' : LaurentSeries (AlgebraicClosure ℚ)) ∧
      An.modulus = ((q : ℕ) : A) ^ 3 := by sorry
