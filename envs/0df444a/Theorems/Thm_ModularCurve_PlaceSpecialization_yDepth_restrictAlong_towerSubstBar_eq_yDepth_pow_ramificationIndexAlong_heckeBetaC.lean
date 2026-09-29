-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerSubstBar_eq_yDepth_pow_ramificationIndexAlong_heckeBetaC
-- name    : ModularCurve.PlaceSpecialization.yDepth_restrictAlong_towerSubstBar_eq_yDepth_pow_ramificationIndexAlong_heckeBetaC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/e1705b6d-e27f-5159-a2b8-fef175abf616
-- title:
--   Depth along the ℓ-substitution leg is a ramification power
-- statement:
--   Let $N\ge 1$, let $q\ge 5$ be a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ is a non-unit of $A$, so that $k=\mathrm{ResidueField}\,A$ has characteristic $q$. Fix a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,k\,N$ over $k$ whose members are exactly the places in $\mathrm{ssPlaces}\,q\,N\,k$ (those satisfying `IsSupersingularPlace`), modular polynomial data `data` at $q$ satisfying the Kronecker congruence $\Phi \bmod q=(X_1^{q}-X_2)(X_1-X_2^{q})$, and the integrality of the two degeneracy maps $\mathrm{heckeAlphaBar}$ and $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$ over $\overline{\mathbb Q}$. Fix a specialisation $P$ of places of the level-$Nq$ geometric function field at $A$ together with a prolongation tuple $R$ over it satisfying the model law (the two divisor laws and the two cusp laws), the order law at the Frobenius-fixed affine places, and the regularity and node-value laws relative to $W$; and, at each $w\in W$, a coefficient field $K_w$ finite over $\mathbb Q$, node coordinates $c_w=(x_w,y_w)$ in the node ring over $K_w$ at $w$, an element $\varpi_w$ of $A\cap K_w$ generating the kernel of the reduction of that ring to $k$, the value-integrality law at $w$, and a crossing presentation $x_wy_w=\mathrm{nodeConst}(\varpi_w)^{E}u$ with $E\ge 1$ and $u$ a unit. Assume the same package one level up for a prime $\ell\ne q$: a finite set $W_r$ of places of $\mathrm{modularFunctionFieldC}\,k\,(N\ell)$ equal to $\mathrm{ssPlaces}\,q\,(N\ell)\,k$, integrality of the two level-$q$ degeneracy maps at level $N\ell$, a specialisation $P_r$ with prolongation tuple $R_r$ satisfying the same five laws relative to $W_r$, and node data $(K_{w},c_{w},\varpi_{w},E,u)$ at each $w\in W_r$ with the same properties. Assume further that the substitution map $\mathrm{towerSubstBar}$ from the level-$Nq$ to the level-$N\ell q$ geometric field (the $\ell$-substitution $\mathrm{heckeBetaBar}$ followed by the tower inclusion, along $Nq\ell\mid N\ell q$) is integral, that $\mathrm{heckeBetaC}\,k\,N\,\ell$ from $\mathrm{modularFunctionFieldC}\,k\,N$ into the roof field $\mathrm{charLDegeneracyRoof}\,k\,N\,\ell$ is integral, and that $\mathrm{modularFunctionFieldC}\,k\,(N\ell)$ is contained in that roof field by an integral inclusion. Then for every place $y_1$ of the roof field, every $y\in W_r$ and $w\in W$ such that $y_1$ restricts to $y$ along the inclusion and to $w$ along $\mathrm{heckeBetaC}$, and every place $V'$ of the level-$N\ell q$ geometric field over $\overline{\mathbb Q}$ with $P_r.\mathrm{reduceFst}\,V'=y$ and $P.\mathrm{reduceFst}$ of the restriction of $V'$ along $\mathrm{towerSubstBar}$ equal to $w$: the depth $A$-valuation of $y_w$ at the restricted place equals the depth of $y_{y}$ at $V'$ raised to the power $y_1.\mathrm{ramificationIndexAlong}(\mathrm{heckeBetaC}\,k\,N\,\ell)$, and the restricted place is strict for $P$ (its first reduction is carried to its second by geometric Frobenius, and is not fixed by the square of Frobenius) if and only if $V'$ is strict for $P_r$.
--
--   This is the transfer, along the $\ell$-substitution leg of the degeneracy tower, of the local picture of the reduction modulo $q$ of $X_0(Nq)$ at a supersingular point: two copies of the level-$N$ curve crossing transversally, with the crossing parameter measured by the depth of the node coordinate $y$. It is used in the proof of the statement computing $\mathrm{yDepth}$ of restrictions along $\mathrm{heckeAlphaBar}$, which feeds the comparison of supersingular node data between levels $N$ and $N\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerSubstBar_eq_yDepth_pow_ramificationIndexAlong_heckeBetaC.lean

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem
    ModularCurve.PlaceSpecialization.yDepth_restrictAlong_towerSubstBar_eq_yDepth_pow_ramificationIndexAlong_heckeBetaC
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
        ∀ (ℓ : Nat.Primes), (ℓ : ℕ) ≠ q →
        haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
        letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A (N * ℓ)
        ∀ (Wᵣ : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) (N * ℓ))))
          (hWᵣ : ∀ w, w ∈ Wᵣ ↔ w ∈ ssPlaces q (N * ℓ) (ResidueField A))
          (hαᵣ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (hβᵣ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * ℓ) q)
          (Pᵣ : PlaceSpecialization A q (N * ℓ) data hKr (ResidueField A) (IsLocalRing.residue A) hαᵣ hβᵣ)
          (Rᵣ : PlaceSpecialization.ProlongationTuple Pᵣ) (hmodelᵣ : Rᵣ.IsModel) (hOᵣ : Rᵣ.OrderLawFixed)
          (hregᵣ : Rᵣ.RegularityLaw Wᵣ) (hvalᵣ : Rᵣ.NodeValueLaw Wᵣ)
          (Ksᵣ : ↥Wᵣ → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥Wᵣ, FiniteDimensional ℚ (Ksᵣ w)]
          (csᵣ : ∀ w : ↥Wᵣ, Rᵣ.NodeCoordinates (Ksᵣ w) (w : Place (ResidueField A) (modularFunctionFieldC
              (ResidueField A) (N * ℓ))))
          (ϖᵣ : ∀ w : ↥Wᵣ, ↥(NodeLocalized.coeffSubring A (Ksᵣ w)))
          (hϖᵣ : ∀ (w : ↥Wᵣ) (d : ↥(NodeLocalized.coeffSubring A (Ksᵣ w))), NodeLocalized.redRestrict
              (IsLocalRing.residue A) (Ksᵣ w) d = 0 ↔ ∃ d', d = ϖᵣ w * d')
          (hvalAᵣ : ∀ w : ↥Wᵣ, Rᵣ.ValueIntegralityLaw (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField
              A) (N * ℓ))))
          (hxyᵣ : ∀ w : ↥Wᵣ, ∃ (E : ℕ) (u : ↥(Rᵣ.nodeIntegersOver (Ksᵣ w) (w : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (N * ℓ))))),
          1 ≤ E ∧ IsUnit u ∧ (csᵣ w).x * (csᵣ w).y = Rᵣ.nodeConst (Ksᵣ w) (w : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (N * ℓ))) (ϖᵣ w) ^ E * u),
        ∀ (hι : (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
                  (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)).toRingHom.IsIntegral)
          (hβC : (heckeBetaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
          (hroof : modularFunctionFieldC (ResidueField A) (N * ℓ) ≤ charLDegeneracyRoof (ResidueField A) N ℓ)
          (hroofι : (IntermediateField.inclusion hroof).toRingHom.IsIntegral)
          (y₁ : Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ))
          (y : ↥Wᵣ) (w : ↥W),
          y₁.restrictAlong (IntermediateField.inclusion hroof) hroofι = (y : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (N * ℓ))) →
          y₁.restrictAlong (heckeBetaC (ResidueField A) N ℓ) hβC = (w : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) N)) →
          ∀ (V' : Place (AlgebraicClosure ℚ)
              (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ * q)))),
            Pᵣ.reduceFst V' = y →
            P.reduceFst (V'.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
                (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)) hι) = w →
            (cs w).yDepth (V'.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
                  (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)) hι)
                = (csᵣ y).yDepth V' ^ y₁.ramificationIndexAlong (heckeBetaC (ResidueField A) N ℓ) ∧
              (P.IsStrictFst (V'.restrictAlong (towerSubstBar (AlgebraicClosure ℚ) (N * q) ℓ
                  (dvd_of_eq (Nat.mul_right_comm N q ℓ) : N * q * ℓ ∣ N * ℓ * q)) hι) ↔ Pᵣ.IsStrictFst V') := by sorry
