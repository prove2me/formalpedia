-- Prove2me | Theorems.Thm_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_zero
-- name    : ModularCurve.NodeLocalized.exists_gaussCoordinate_of_crossingPresentation_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/bb832a53-9750-5fa2-a511-c259f305dead
-- title:
--   Gauss coordinate at a supersingular centre j=0
-- statement:
--   Fix a prime $q$ with $q \ge 5$, a valuation subring $A$ of $\overline{\mathbb Q}$, and a field $k$ of characteristic $q$ with decidable equality, together with a ring homomorphism $\mathrm{red} : A \to k$ whose vanishing locus is exactly the maximal ideal of $A$, and assume $0 \in k$ is supersingular in the sense of `ssJSet q k`: every elliptic Weierstrass curve over $k$ with $j$-invariant $0$ has no nonzero point killed by $q$. Let $K$ be a finite extension of $\mathbb Q$ inside $\overline{\mathbb Q}$, put $A_K = A \cap K$ (the subring `coeffSubring A K`), let $\varpi \in A_K$ be such that an element of $A_K$ reduces to $0$ under the restricted map `redRestrict red K` precisely when it is a multiple of $\varpi$, and write $q = \varpi^{e_K}\varepsilon$ with $e_K \ge 1$ and $\varepsilon$ a unit of $A_K$. Let $R$ be the subring `modularLocalizedAtPoint (1 * q) A_K (redRestrict red K) 0 (0^q)` of Laurent series over $\overline{\mathbb Q}$, consisting of those $f$ with $f \cdot \mathrm{modularEval}(s) = \mathrm{modularEval}(r)$ for some $r, s \in A_K[X_0, X_1]$ whose $s$ has nonvanishing `pointEval` at $(0, 0^q)$, where $\mathrm{modularEval}$ substitutes the $q$-expansions of $j$ and of $j(q\,\cdot)$ for $X_0, X_1$ and constants via `constSeries`. Let $G', H', w \in R$ with $w$ a unit, $G'H' = \varpi^{\,\mathrm{jWidth}(0)\cdot e_K} w$ (and $\mathrm{jWidth}(0) = 3$), where $\varpi$ denotes the constant series $\mathrm{modularEval}(C\,\varpi)$; assume the ideals $(\varpi, G')$ and $(\varpi, H')$ of $R$ are prime, that $H' \notin (\varpi, G')$ and $G' \notin (\varpi, H')$, and that $(\varpi, G') = (\varpi, \mathrm{modularEval}(X_1 - X_0^q))$ and $(\varpi, H') = (\varpi, \mathrm{modularEval}(X_0 - X_1^q))$. Then there is $G_f$ in `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $q$ inside $\mathrm{LaurentSeries}(\overline{\mathbb Q})$, equal to $G'$ as a Laurent series, such that $\bigl(q^{\,\mathrm{jWidth}(0)}\bigr)^{-1} \cdot G_f$ and $\mathrm{frickeInvolutionBar}(1 * q)(G_f)$ both lie in `CharPReduction.modularLocalized (1 * q) A.toSubring red`, both have nonzero image under `CharPReduction.modularRedLocHom (1 * q) A.toSubring red`, and for every place $W$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ such that there exist $x, y \in A$ with $\mathrm{red}\,x = 0$, $\mathrm{red}\,y = 0^q$, $W.\mathrm{ord}(j - x) > 0$ and $W.\mathrm{ord}(j_q - y) > 0$ (where $j$ and $j_q$ are the images of `jq` and of `qExpand ℚ (1 * q) jq` under the coefficient embedding), one has $W.\mathrm{ord}(G_f) = 0$.
--
--   This packages a crossing presentation of the node of width $3$ at the supersingular point $j = 0$ on the reduction of $X_0(q)$ into a single global function $G_f$ on $X_0(q)_{/\overline{\mathbb Q}}$: after dividing by $q^3$ it is regular with nonzero reduction at one end of the node, its Fricke transform is regular with nonzero reduction at the other end, and it has neither zero nor pole at any place of the tube over the node. It is used in the construction of two-branch normalisations and of the admissible representatives of cuspidal classes in the level-one prolongation argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_NodeLocalized_exists_gaussCoordinate_of_crossingPresentation_zero.lean

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

theorem ModularCurve.NodeLocalized.exists_gaussCoordinate_of_crossingPresentation_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (ha : (0 : k) ∈ ssJSet q k) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε) (heK1 : 1 ≤ eK)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) (0 : k) ((0 : k) ^ q))) ^ (jWidth (0 : k) * eK) * w)
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
    ∃ (Gf : ↥(modularFunctionFieldBar (1 * q))) (_ : (Gf : LaurentSeries (AlgebraicClosure ℚ)) = (G' : LaurentSeries (AlgebraicClosure ℚ)))
      (hG₁ : (((((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth (0 : k))⁻¹ • Gf : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red)
      (hG₂ : ((frickeInvolutionBar (1 * q) Gf : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₁⟩ ≠ 0 ∧
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hG₂⟩ ≠ 0 ∧
        ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = (0 : k) ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
            (∃ y : A, red y = (0 : k) ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord Gf = 0 := by sorry
