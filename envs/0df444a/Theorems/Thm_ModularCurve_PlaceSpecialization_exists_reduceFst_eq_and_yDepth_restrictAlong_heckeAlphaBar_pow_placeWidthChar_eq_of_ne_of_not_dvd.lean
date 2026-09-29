-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_placeWidthChar_eq_of_ne_of_not_dvd
-- name    : ModularCurve.PlaceSpecialization.exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_placeWidthChar_eq_of_ne_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/c173fd05-e4fb-5154-a159-fdcc697cb4d0
-- title:
--   Cross-power law for node depths along the level-ℓ Hecke roof
-- statement:
--   Fix $N\ge 1$ and a prime $q$ with $q\nmid N$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ is a non-unit of $A$; its residue field $k=\mathrm{ResidueField}\,A$ then has characteristic $q$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ over $k$ whose members are exactly the supersingular places, i.e. those $w$ that are rational, have both $j$ and $j_N$ in the valuation subring, and have $j$-value in $\mathrm{ssJSet}\,q$. Fix modular polynomial data at $q$ whose bivariate reduction mod $q$ equals $(\mathrm{C}\,X^q-X)(\mathrm{C}\,X-X^q)$, integrality of the two degeneracy embeddings $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$, a place specialisation $P$ of the level-$Nq$ function field at $A$ onto the level-$N$ function field over $k$, and a prolongation tuple $R$ for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), `OrderLawFixed`, and the regularity and node-value laws relative to $W$. Assume given, for each $w\in W$: a number field $K_w\subset\overline{\mathbb{Q}}$, node coordinates $c_w=(x_w,y_w)$ in $R.\mathrm{nodeIntegersOver}\,K_w\,w$, an element $\varpi_w$ of the coefficient ring $A\cap K_w$ such that an element of that ring reduces to $0$ under $\mathrm{redRestrict}$ of the residue map of $A$ precisely when it is a multiple of $\varpi_w$, the value-integrality law at $w$, and a crossing presentation $x_w y_w = (\mathrm{nodeConst}\,\varpi_w)^{E}u$ with $E\ge 1$ and $u$ a unit. The assertion: for every prime $\ell\ne q$ with $\ell\nmid N$, every pair of integrality hypotheses for $\mathrm{heckeAlphaBar}$ and $\mathrm{heckeBetaBar}$ from level $Nq$ to level $Nq\ell$, every place $V'$ of the level-$Nq\ell$ function field over $\overline{\mathbb{Q}}$, and every $w\in W$ with $P.\mathrm{reduceFst}$ of the restriction of $V'$ along $\mathrm{heckeBetaBar}$ equal to $w$, there is $w''\in W$ with $P.\mathrm{reduceFst}$ of the restriction of $V'$ along $\mathrm{heckeAlphaBar}$ equal to $w''$, and, in the value group of $A$, the $y$-depth of $c_{w''}$ at the $\alpha$-restriction raised to the power $\mathrm{placeWidthChar}\,q\,N\,w$ equals the $y$-depth of $c_w$ at the $\beta$-restriction raised to the power $\mathrm{placeWidthChar}\,q\,N\,w''$, where the $y$-depth of node coordinates at a place is the $A$-valuation of the value of $y$ there, and $\mathrm{placeWidthChar}\,q\,N$ is the characteristic-aware width $j$-invariant datum ($12$ or $6$ at $j=0$ for $q=2,3$ respectively, otherwise the tame width) divided by the ramification index over the $j$-line.
--
--   This is the transport law for node depths at the supersingular points of the reduction of the level-$Nq$ modular curve along the two degeneracy maps of a further level structure at a prime $\ell\nmid Nq$, in the form of an equality of cross-powers weighted by the characteristic-aware widths, valid in every residue characteristic including $q=2,3$. It feeds the computation of the Hecke action on the component group of the Jacobian at $q$ used in level lowering, being cited by [`ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv`](thm.html#ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_placeWidthChar_eq_of_ne_of_not_dvd.lean

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_placeWidthChar_eq_of_ne_of_not_dvd
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
      (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
      (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
      (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (ϖ : ∀ w : ↥W, ↥(NodeLocalized.coeffSubring A (Ks w)))
      (hϖ : ∀ (w : ↥W) (d : ↥(NodeLocalized.coeffSubring A (Ks w))), NodeLocalized.redRestrict (IsLocalRing.residue A) (Ks w) d = 0 ↔ ∃ d', d = ϖ w * d')
      (hvalA : ∀ w : ↥W, R.ValueIntegralityLaw (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hxy : ∀ w : ↥W, ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))),
        1 ≤ E ∧ IsUnit u ∧ (cs w).x * (cs w).y = R.nodeConst (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (ϖ w) ^ E * u),
        ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ≠ q → ¬ (ℓ : ℕ) ∣ N →
        haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
        ∀ (hα' : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
          (hβ' : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
          (V' : Place (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q * ℓ))))
          (w : ↥W),
          P.reduceFst (V'.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβ') = w →
          ∃ w'' : ↥W,
            P.reduceFst (V'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hα') = w'' ∧
            (cs w'').yDepth (V'.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hα')
                ^ placeWidthChar q N (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
              = (cs w).yDepth (V'.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβ')
                ^ placeWidthChar q N (w'' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) := by sorry
