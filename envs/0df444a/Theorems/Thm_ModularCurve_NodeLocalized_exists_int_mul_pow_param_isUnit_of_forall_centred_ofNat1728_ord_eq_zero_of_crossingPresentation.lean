-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation
-- name    : ModularCurve.NodeLocalized.exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/ec535a2f-4017-5c6f-8625-5a766c831bf8
-- title:
--   Unit principle at the width-two supersingular node j = 1728
-- statement:
--   Fix a prime $q$ with $5 \le q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ (realised as `AlgebraicClosure ℚ`), and an algebraically closed field $k$ of characteristic $q$, together with a ring homomorphism $\mathrm{red} : A \to k$.
--
--   *Reduction data.* The hypothesis `hker` says that $\mathrm{red}$ has kernel exactly the maximal ideal of $A$, i.e. $\mathrm{red}\,c = 0$ if and only if $c \in \mathfrak{m}_A$. The hypothesis `ha` says that $1728 \in k$ lies in `ssJSet q k`, which by definition means: every elliptic curve $W$ over $k$ with $j$-invariant $1728$ has the property that every affine point $P$ of $W$ with $q \cdot P = 0$ is $0$ (no nontrivial $q$-torsion). The hypothesis `hq` is $5 \le q$.
--
--   *Coefficient ring and uniformiser.* $K$ is a finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, and `coeffSubring A K` denotes the subring $A \cap K$ of $\overline{\mathbb{Q}}$; `redRestrict red K` is the composite of the inclusion $A \cap K \hookrightarrow A$ with $\mathrm{red}$. An element $\varpi \in A \cap K$ is given such that, by `hϖ`, the kernel of `redRestrict red K` is the principal ideal $(\varpi)$: an element $c$ reduces to $0$ exactly when $c = \varpi d$ for some $d$. A natural number $e_K$ and a unit $\varepsilon$ of $A \cap K$ are given with $q = \varpi^{e_K}\varepsilon$ in $A \cap K$ (`hqϖ`, `hε`) and $1 \le e_K$ (`heK1`).
--
--   *The node ring.* Let $R :=$ `modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)`, the subring of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ consisting of those Laurent series $f$ for which there are two-variable polynomials $r, s \in (A\cap K)[X_0, X_1]$ with $s$ not vanishing at the point $(1728, 1728^q)$ in the sense of `pointEval` and $f \cdot \mathrm{modularEval}(s) = \mathrm{modularEval}(r)$; here `modularEval (1 * q) (coeffSubring A K)` is the evaluation homomorphism $(A\cap K)[X_0,X_1] \to \mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ sending constants to constant series (`constSeries`), $X_0$ to `jqModC` and $X_1$ to `jqNModC` at level $1 \cdot q$. Write $\pi \in R$ for the element $\mathrm{modularEval}(\mathrm{C}\,\varpi)$, the constant series attached to $\varpi$.
--
--   *Crossing presentation.* Elements $G', H', w \in R$ are given with $w$ a unit (`hw`) and, by `hGH`,
--   $$G' H' = \pi^{\,\mathrm{jWidth}(1728)\cdot e_K} \, w,$$
--   where `jWidth j` is $3$ for $j = 0$, $2$ for $j = 1728$ and $1$ otherwise, so that the exponent is $2 e_K$ in the present characteristic. The hypothesis `hmax` says that, for any local ring structure on $R$, the maximal ideal of $R$ is the ideal spanned by $\{\pi, G', H'\}$.
--
--   *Branch ideals.* The two ideals $(\pi, G')$ and $(\pi, H')$ of $R$ are prime (`hpr1`, `hpr2`); $H' \notin (\pi, G')$ (`hnm1`) and $G' \notin (\pi, H')$ (`hnm2`); and the two branches are identified with the two coordinate branches through the node: $(\pi, G') = (\pi, \mathrm{modularEval}(X_1 - X_0^q))$ (`hsp1`) and $(\pi, H') = (\pi, \mathrm{modularEval}(X_0 - X_1^q))$ (`hsp2`).
--
--   *Centred places.* Let $\mathcal{F} :=$ `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1 \cdot q$, viewed as an intermediate field of $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ over $\overline{\mathbb{Q}}$. A place $W$ of $\mathcal{F}$ over $\overline{\mathbb{Q}}$ is a valuation subring of $\mathcal{F}$ containing $\overline{\mathbb{Q}}$, distinct from $\mathcal{F}$, whose ring is a principal ideal ring; $W.\mathrm{ord}$ is minus the logarithm of the associated adic valuation, and $W.\mathrm{evalAt}$ is the residue map followed by the inverse of $\overline{\mathbb{Q}} \to$ residue field (and $0$ off the valuation subring). Call $W$ *centred* when both of the following hold: there is $x \in A$ with $\mathrm{red}\,x = 1728$ and $W.\mathrm{ord}(j - x) > 0$, where $j \in \mathcal{F}$ is the coefficientwise image `coeffEmb (AlgebraicClosure ℚ) jq` of the $q$-expansion of the modular invariant; and there is $y \in A$ with $\mathrm{red}\,y = 1728^q$ and $W.\mathrm{ord}(j_q - y) > 0$, where $j_q \in \mathcal{F}$ is the coefficientwise image of `qExpand ℚ (1 * q) jq`.
--
--   *Conclusion.* Under these hypotheses, for every $G_f \in \mathcal{F}$ whose underlying Laurent series equals that of $G'$, and for every $f \in \mathcal{F}$ with $f \neq 0$ such that $W.\mathrm{ord}\,f = 0$ for every centred place $W$, there exist an integer $m$ and an element $c \in \overline{\mathbb{Q}}$ with $c \neq 0$ such that for every centred place $W$ the element
--   $$W.\mathrm{evalAt}(f) \cdot c^{-1} \cdot \bigl(W.\mathrm{evalAt}(G_f)\bigr)^{-m}$$
--   of $\overline{\mathbb{Q}}$ lies in $A$ and is a unit of $A$.
--
--   This is the unit (Gauss-normalisation) principle on the supersingular tube of $X_0(q)$ centred at $j = 1728$, the node of width two, the companion of the width-three statement at $j = 0$: a nonzero modular function with vanishing order at every place centred at the node becomes, after rescaling by a constant and by an integral power of the branch parameter $G'$, a unit at every such place. It is used by [`ModularCurve.exists_ssAnnulus_centred_ofNat1728_of_crossingPresentation_of_branchPrimes`](thm.html#ModularCurve.exists_ssAnnulus_centred_ofNat1728_of_crossingPresentation_of_branchPrimes) in the analysis of the $q$-adic geometry of $X_0(q)$ near supersingular points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation.lean

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

theorem ModularCurve.NodeLocalized.exists_int_mul_pow_param_isUnit_of_forall_centred_ofNat1728_ord_eq_zero_of_crossingPresentation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (ha : (1728 : k) ∈ ssJSet q k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))) ^ (jWidth (1728 : k) * eK) * w)
    (hmax : ∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))],
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q)) =
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (1728 : k) ((1728 : k) ^ q))), G', H'})
    (heK1 : 1 ≤ eK)
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
∀ Gf : ↥(modularFunctionFieldBar (1 * q)),
      (Gf : LaurentSeries (AlgebraicClosure ℚ)) = (G' : LaurentSeries (AlgebraicClosure ℚ)) →
        ∀ f : ↥(modularFunctionFieldBar (1 * q)), f ≠ 0 →
          (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
            ((∃ x : A, red x = (1728 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (1728 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0) →
          ∃ (m : ℤ) (c : AlgebraicClosure ℚ), c ≠ 0 ∧
            ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
              ((∃ x : A, red x = (1728 : k) ∧
              0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
              (∃ y : A, red y = (1728 : k) ^ q ∧
              0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
                ∃ h : W.evalAt f * c⁻¹ * (W.evalAt Gf) ^ (-m) ∈ A, IsUnit (⟨_, h⟩ : A) := by sorry
