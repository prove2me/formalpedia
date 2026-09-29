-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_width_eq_of_ne_of_not_dvd
-- name    : ModularCurve.PlaceSpecialization.exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_width_eq_of_ne_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/7a4af466-dbf7-5e1e-9093-661d81c2c864
-- title:
--   Cross-power law for node depths under the ℓ-degeneracy maps
-- statement:
--   Fix $N \ge 1$ and a prime $q \ge 5$ with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, so that its residue field $k =$ `ResidueField A` has characteristic $q$. Let $W$ be a finite set of places of $\mathtt{modularFunctionFieldC}\,k\,N$ over $k$ whose members are exactly the elements of $\mathtt{ssPlaces}\ q\ N\ k$, i.e. the places that are rational, have both $j$-generators in their valuation subring, and whose $j$-value lies in the supersingular set $\mathtt{ssJSet}\ q\ k$. Fix modular polynomial data at $q$ with $\Phi \bmod q = (C X^{q} - X)(C X - X^{q})$; assume the two degeneracy maps $\mathtt{heckeAlphaBar}$ (inclusion) and $\mathtt{heckeBetaBar}$ ($q$-expansion substitution) from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$ are integral; and fix a `PlaceSpecialization` $P$ at $A$ together with a `ProlongationTuple` $R$ over it satisfying `IsModel` (the two divisor laws and the two cusp laws), `OrderLawFixed`, and the `RegularityLaw` and `NodeValueLaw` at $W$. For each $w \in W$ fix an intermediate field $K_w$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$, node coordinates $c_w = (x_w, y_w)$ in $R.\mathtt{nodeIntegersOver}\ K_w\ w$, an element $\varpi_w$ of $A \cap K_w$ generating the kernel of the reduction $A \cap K_w \to k$ in the sense that an element reduces to $0$ precisely when it is a multiple of $\varpi_w$, the value-integrality law at $w$, and a crossing presentation $x_w y_w = (\mathtt{nodeConst}\,\varpi_w)^{E} u$ with $E \ge 1$ and $u$ a unit. Then for every prime $\ell \neq q$ with $\ell \nmid N$, every pair of integrality hypotheses for the two level-$\ell$ degeneracy maps from level $Nq$ to level $Nq\ell$ over $\overline{\mathbb{Q}}$, every place $V'$ of the level-$Nq\ell$ base-changed field over $\overline{\mathbb{Q}}$, and every $w \in W$ such that $P.\mathtt{reduceFst}$ of the restriction of $V'$ along $\mathtt{heckeBetaBar}$ equals $w$, there is $w'' \in W$ with $P.\mathtt{reduceFst}$ of the restriction of $V'$ along $\mathtt{heckeAlphaBar}$ equal to $w''$, and, in the value group of $A$, $$\big(\text{yDepth}_{c_{w''}}(V'|_{\alpha'})\big)^{\,\mathtt{placeWidth}\,N\,w} = \big(\text{yDepth}_{c_{w}}(V'|_{\beta'})\big)^{\,\mathtt{placeWidth}\,N\,w''},$$ where the depth of a place is the $A$-valuation of the value of the coordinate $y$ at that place, and $\mathtt{placeWidth}\,N$ of a place is $\mathtt{jWidth}$ of its $j$-value divided by its ramification index over the $j$-line.
--
--   This expresses, in the function-field formalism for the reduction of $X_0(Nq)$ at $q$ with its two components crossing at the supersingular points (Deligne–Rapoport), that the two level-$\ell$ degeneracy maps send places above a supersingular annulus to places above a supersingular annulus, with the node depths related by the cross-power law weighted by the widths of the two supersingular places. It feeds the computation of the Hecke action on the component group of the Jacobian at $q$, used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_width_eq_of_ne_of_not_dvd.lean

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidth
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

theorem
ModularCurve.PlaceSpecialization.exists_reduceFst_eq_and_yDepth_restrictAlong_heckeAlphaBar_pow_width_eq_of_ne_of_not_dvd
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N) (hq5 : 5 ≤ q)
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
                ^ placeWidth N (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
              = (cs w).yDepth (V'.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβ')
                ^ placeWidth N (w'' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) := by sorry
