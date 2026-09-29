-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation
-- name    : ModularCurve.NodeLocalized.exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/50302cc6-1399-5037-a366-b3a9a5c6f19b
-- title:
--   Elements of order zero at a node are monomials
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$ with decidable equality, a ring homomorphism $\mathrm{red}:A\to k$, and $a\in k$ with $a^{q^{2}}=a$. Let $K\subseteq\overline{\mathbb{Q}}$ be a finite extension of $\mathbb{Q}$, put $A_{0}=A\cap K$ (`coeffSubring`) with the induced reduction $A_{0}\to k$, and assume: some $x\in A_{0}$ reduces to $a$; some $\varpi\in A_{0}$ is such that an element of $A_{0}$ reduces to $0$ exactly when it is a multiple of $\varpi$; and $q=\varpi^{e_{K}}\varepsilon$ with $e_{K}\ge 1$ and $\varepsilon$ a unit. Let $R_{0}$ be the subring `modularLocalizedAtPoint` of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ consisting of those $f$ with $f\cdot E(s)=E(r)$ for some $r,s$ in $A_{0}[X_{0},X_{1}]$ with $s$ not vanishing at $(a,a^{q})$ after reduction, where $E$ evaluates $X_{0}$ at the $q$-expansion $j$ and $X_{1}$ at its $q$-fold rescaling $j_{q}$, constants being constant series; write $\Pi=E(\varpi)\in R_{0}$. Assume given $G',H',w\in R_{0}$ with $w$ a unit, $G'H'=\Pi^{\,\mathrm{jWidth}(a)\,e_{K}}w$, where $\mathrm{jWidth}(a)$ is $3,2,1$ according as $a=0$, $a=1728$, or otherwise; that for any local-ring structure on $R_{0}$ the maximal ideal is $(\Pi,G',H')$; that $(\Pi,G')$ and $(\Pi,H')$ are prime with $H'\notin(\Pi,G')$ and $G'\notin(\Pi,H')$; and that $(\Pi,G')=(\Pi,E(X_{1}-X_{0}^{q}))$, $(\Pi,H')=(\Pi,E(X_{0}-X_{1}^{q}))$. Let $g\in R_{0}$ be nonzero whose underlying Laurent series lies in the function field $\overline{\mathbb{Q}}\cdot F_{\mathrm{full}}(q)$ (`modularFunctionFieldBar`), and suppose $\mathrm{ord}_{W}(g)=0$ for every place $W$ of that field over $\overline{\mathbb{Q}}$ which is centred at the node, i.e. for which there are $x,y\in A$ with $\mathrm{red}(x)=a$, $\mathrm{red}(y)=a^{q}$ and $\mathrm{ord}_{W}(j-x)>0$, $\mathrm{ord}_{W}(j_{q}-y)>0$. Then there are $l,i,j\in\mathbb{N}$ and a unit $u\in R_{0}$ with $g=\Pi^{l}H'^{i}G'^{j}u$.
--
--   This is the monomial description of functions with no zeros or poles away from the branches at a supersingular node of the plane model of $X_0(q)$: the local ring at such a node has the crossing shape $G'H'=\varpi^{we}\cdot(\text{unit})$ familiar from the Deligne–Rapoport and Katz–Mazur local analysis, and an element of order zero at all places centred on the node is a product of powers of the uniformiser and of the two branch parameters times a unit. It feeds the two-branch normalisation statements [`ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_ofNat1728_width_dvd`](thm.html#ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_ofNat1728_width_dvd) and [`ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_zero_width_dvd`](thm.html#ModularCurve.NodeLocalized.exists_twoBranchNormalisation_qpow_zero_width_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.NodeLocalized.exists_isUnit_and_eq_pow_mul_pow_mul_pow_mul_of_forall_centred_ord_eq_zero_of_crossingPresentation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha2 : a ^ (q ^ 2) = a)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (heK1 : 1 ≤ eK) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ (jWidth a * eK) * w)
    (hmax : ∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
        IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
          Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'})
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}).IsPrime)
    (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))})
    (g : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hg0 : g ≠ 0)
    (hgF : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q))
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord (⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hgF⟩ : modularFunctionFieldBar (1 * q)) = 0) :
    ∃ (l i j : ℕ) (u : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), IsUnit u ∧
      g = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
        modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ l *
        H' ^ i * G' ^ j * u := by sorry
