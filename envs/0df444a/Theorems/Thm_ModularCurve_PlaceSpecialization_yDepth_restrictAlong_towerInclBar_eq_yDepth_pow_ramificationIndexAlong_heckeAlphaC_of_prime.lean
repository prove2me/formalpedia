-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerInclBar_eq_yDepth_pow_ramificationIndexAlong_heckeAlphaC_of_prime
-- name    : ModularCurve.PlaceSpecialization.yDepth_restrictAlong_towerInclBar_eq_yDepth_pow_ramificationIndexAlong_heckeAlphaC_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/a06bcc19-38a9-5cb8-9342-61dfccb8782f
-- title:
--   Node depth along the ℓ-degeneracy leg is a ramified power
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime with $q\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$; its residue field $k=\mathrm{ResidueField}\,A$ then has characteristic $q$. Fix a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places `ssPlaces q N k`, modular polynomial data at $q$ satisfying the Kronecker congruence, integrality of the two level-$q$ degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` at level $N$, a place specialisation $P$ of the level-$Nq$ situation at $A$ with reduction map the residue map of $A$, and a prolongation tuple $R$ over $P$ satisfying `IsModel`, `OrderLawFixed`, and the regularity and node-value laws for $W$. For each $w\in W$ fix a finite extension $K_w$ of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, node coordinates $c_w=(x_w,y_w)$ over $K_w$ at $w$, an element $\varpi_w$ of the coefficient subring $A\cap K_w$ such that an element of that subring reduces to $0$ under `redRestrict` exactly when it is a multiple of $\varpi_w$, the value-integrality law at $w$, and a factorisation $x_w y_w=\mathrm{nodeConst}(\varpi_w)^{E}u$ with $E\ge 1$ and $u$ a unit of the ring $R.\mathrm{nodeIntegersOver}\,K_w\,w$. Assume the same package of data and laws at level $N\ell$ for a prime $\ell\ne q$ (with set $W_{\mathrm r}$ of supersingular places, specialisation $P_{\mathrm r}$, tuple $R_{\mathrm r}$, fields $K_{\mathrm r,y}$, coordinates $c_{\mathrm r,y}$, uniformisers $\varpi_{\mathrm r,y}$, summarised here), together with integrality of the tower inclusion for $Nq\mid N\ell q$, of `heckeAlphaC k N ℓ` into the roof $\mathrm{charLDegeneracyRoof}\,k\,N\,\ell$, and of the inclusion of $\mathrm{modularFunctionFieldC}\,k\,(N\ell)$ into that roof, the latter containment being hypothesised. Let $y_1$ be a place of the roof, $y\in W_{\mathrm r}$ and $w\in W$ with $y_1$ restricting to $y$ along the roof inclusion and to $w$ along `heckeAlphaC`. Then for every place $V'$ of the base-changed level-$N\ell q$ field over $\overline{\mathbb{Q}}$ with $P_{\mathrm r}.\mathrm{reduceFst}\,V'=y$ and $P.\mathrm{reduceFst}$ of the restriction of $V'$ along the tower inclusion equal to $w$, the depth $A$-valuation of $y_w$ at that restriction equals the corresponding depth of $y_{\mathrm r,y}$ at $V'$ raised to the ramification index of $y_1$ along `heckeAlphaC`, and the restriction of $V'$ is strict for $P$ on the first leg if and only if $V'$ is strict for $P_{\mathrm r}$.
--
--   This is the comparison, across the forgetful degeneracy leg from level $N\ell$ to level $N$, of the node depths attached to the supersingular crossing points in the reduction at $q$ of the $\Gamma_0(q)$-structure, in the style of the Deligne–Rapoport description of that reduction as two copies of the level-$N$ curve crossing at the supersingular points. It feeds the construction of places with prescribed first reduction and depth used in the level-raising/level-lowering analysis at level $N\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_yDepth_restrictAlong_towerInclBar_eq_yDepth_pow_ramificationIndexAlong_heckeAlphaC_of_prime.lean

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
    ModularCurve.PlaceSpecialization.yDepth_restrictAlong_towerInclBar_eq_yDepth_pow_ramificationIndexAlong_heckeAlphaC_of_prime
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
        ∀ (hι : (towerInclBar (AlgebraicClosure ℚ)
                  (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)).toRingHom.IsIntegral)
          (hαC : (heckeAlphaC (ResidueField A) N ℓ).toRingHom.IsIntegral)
          (hroof : modularFunctionFieldC (ResidueField A) (N * ℓ) ≤ charLDegeneracyRoof (ResidueField A) N ℓ)
          (hroofι : (IntermediateField.inclusion hroof).toRingHom.IsIntegral)
          (y₁ : Place (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ))
          (y : ↥Wᵣ) (w : ↥W),
          y₁.restrictAlong (IntermediateField.inclusion hroof) hroofι = (y : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) (N * ℓ))) →
          y₁.restrictAlong (heckeAlphaC (ResidueField A) N ℓ) hαC = (w : Place (ResidueField A)
              (modularFunctionFieldC (ResidueField A) N)) →
          ∀ (V' : Place (AlgebraicClosure ℚ)
              (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ * q)))),
            Pᵣ.reduceFst V' = y →
            P.reduceFst (V'.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
                (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hι) = w →
            (cs w).yDepth (V'.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
                  (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hι)
                = (csᵣ y).yDepth V' ^ y₁.ramificationIndexAlong (heckeAlphaC (ResidueField A) N ℓ) ∧
              (P.IsStrictFst (V'.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
                  (mul_dvd_mul_right (dvd_mul_right N ℓ) q : N * q ∣ N * ℓ * q)) hι) ↔ Pᵣ.IsStrictFst V') := by sorry
