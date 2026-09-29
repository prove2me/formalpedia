-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_ofNat1728
-- name    : ModularCurve.NodeLocalized.exists_gaussCoordinate_of_crossingPresentation_ofNat1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/b89f5998-f3f0-5271-91e3-a7ddca36b128
-- title:
--   Gauss coordinate at a supersingular node with j=1728
-- statement:
--   Fix a prime $q\ge 5$, a valuation subring $A$ of $\overline{\mathbb Q}$ and a field $k$ of characteristic $q$ together with a ring homomorphism $\mathrm{red}\colon A\to k$ whose zero set is exactly the maximal ideal of $A$, and assume $1728\in k$ lies in `ssJSet q k`, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $1728$ has no nonzero point $P$ with $q\cdot P=0$. Let $K\subset\overline{\mathbb Q}$ be a number field, put $A_K=A\cap K$, let $\varpi\in A_K$ be such that an element of $A_K$ reduces to $0$ precisely when it is a multiple of $\varpi$, and write $q=\varpi^{e_K}\varepsilon$ with $e_K\ge 1$ and $\varepsilon$ a unit of $A_K$. Let $R=$ `modularLocalizedAtPoint (1 * q) A_K (redRestrict red K) 1728 (1728 ^ q)`, the subring of Laurent series $f$ over $\overline{\mathbb Q}$ admitting $r,s\in A_K[X_0,X_1]$ with $s$ not vanishing at $(1728,1728^q)$ after reduction and $f\cdot s(j,j_q)=r(j,j_q)$, where $j,j_q$ denote the $q$-expansions of $j$ and of $j$ at level $q$; thus $R$ is the local ring of the plane model $A_K[j,j_q]$ at that point of the special fibre. Let $G',H',w\in R$ with $w$ a unit and $G'H'=\varpi^{\,\mathrm{jWidth}(1728)\,e_K}w$, where $\mathrm{jWidth}(1728)=2$; assume the ideals $(\varpi,G')$ and $(\varpi,H')$ of $R$ are prime, that $H'\notin(\varpi,G')$ and $G'\notin(\varpi,H')$, and that $(\varpi,G')=(\varpi,\,j_q-j^{\,q})$ and $(\varpi,H')=(\varpi,\,j-j_q^{\,q})$. The conclusion asserts the existence of an element $G_f$ of the base change `modularFunctionFieldBar (1 * q)` of the full level-$q$ modular function field to $\overline{\mathbb Q}$, equal to $G'$ as a Laurent series, such that: $(q^{\,\mathrm{jWidth}(1728)})^{-1}\cdot G_f$ and $\mathrm{frickeInvolutionBar}(1\cdot q)(G_f)$ both lie in `CharPReduction.modularLocalized (1 * q) A.toSubring red`, the localisation of the level-$q$ modular ring with coefficients in $A$ at the kernel of coefficientwise reduction; the images of both under the induced homomorphism `modularRedLocHom` to Laurent series over $k$ are nonzero; and for every place $W$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ (a proper valuation subring containing $\overline{\mathbb Q}$ and a principal ideal ring) which is centred at the point, in the sense that there are $x,y\in A$ with $\mathrm{red}\,x=1728$, $\mathrm{red}\,y=1728^q$ and $W.\mathrm{ord}(j-x)>0$, $W.\mathrm{ord}(j_q-y)>0$, one has $W.\mathrm{ord}(G_f)=0$.
--
--   This is the $j=1728$ case (node width $2$) of the construction of a two-ended parameter, or Gauss coordinate, at a supersingular node of the Deligne–Rapoport model of $X_0(q)$: from a crossing presentation $G'H'=\varpi^{2e_K}w$ of the node in the local ring of the plane model $A_K[j,j_q]$ it produces a modular function which is regular with nonzero reduction at both ends, after dividing out $q^2$ on the branch cut out by $G'$, and which is free of zeros and poles on the tube over the node. It feeds the normalisation statements for the width-$2$ node and the prolongation-pair analysis of places over that point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_ofNat1728.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeLocalizedPresentation
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_StandardAnnulus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

theorem ModularCurve.NodeLocalized.exists_gaussCoordinate_of_crossingPresentation_ofNat1728
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ha : (1728 : k) ∈ ssJSet q k) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε) (heK1 : 1 ≤ eK)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) ^ (jWidth (1728 : k) * eK) * w)
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'}).IsPrime)
    (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))}) :
    ∃ (Gf : ↥(modularFunctionFieldBar (1 * q))) (_ : (Gf : LaurentSeries (AlgebraicClosure ℚ)) = (G' : LaurentSeries (AlgebraicClosure ℚ)))
      (hG₁ : (((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (1728 : k))⁻¹ • Gf : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (hG₂ : ((frickeInvolutionBar (1 * q) Gf : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₁⟩ ≠ 0 ∧
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₂⟩ ≠ 0 ∧
        ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = (1728 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (1728 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord Gf = 0 := by sorry
