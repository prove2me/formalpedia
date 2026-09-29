-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_goodRep_admissible_smul_single_sub_self_of_ne_zero_of_ne
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_goodRep_admissible_smul_single_sub_self_of_ne_zero_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/d4476b39-ef26-5bfc-9fdf-6207f211e3e5
-- title:
--   Good admissible representative of σ V-V at a supersingular node
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of $\overline{\mathbb Q}$ whose residue field $\kappa=\mathrm{ResidueField}\,A$ has characteristic $q$, together with modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses $h\alpha,h\beta$ for the two degeneracy embeddings $\overline{F}_1\to\overline{F}_{1\cdot q}$, and a place specialization $P$ from places of $\mathrm{modularFunctionFieldBar}\,1$ to places of $\mathrm{modularFunctionFieldC}\,\kappa\,1$ along the residue map of $A$. Let $R$ be a level-one prolongation pair for $P$ subject to: `R.IsModel` (the two divisor laws and the cusp laws at $\infty$ and at $0$), `R.OrderLawFixed` (the order law at places fixed by the square of the geometric-level Frobenius and distinct from the reduction of the cusp $\infty$), the node value law `hval` for $q$ and the residue map of $A$, and the regularity law `R.RegularityLaw S₀`, where $S_0$ is a finite set enumerating $\mathrm{ssJSet}\,q\,\kappa$, the set of $j\in\kappa$ such that every elliptic Weierstrass curve over $\kappa$ with $j$-invariant $j$ has no nonzero $q$-torsion point. Let $W$ be a finite set enumerating the supersingular places $\mathrm{ssPlaces}\,q\,1\,\kappa$. Let $\sigma$ be a $\mathbb Q$-automorphism of $\overline{\mathbb Q}$ in the inertia subgroup of $A$ over $\mathbb Q$, and $V$ a place of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ which is neither strict of the first kind nor strict of the second kind for $P$, whose first reduction $P.\mathrm{reduceFst}\,V$ lies in $W$ and equals $\mathrm{charLGeomPlaceOfPoint}\,\kappa\,a$, the first member of $\mathrm{frobNodePair}\,q\,a$, for some $a\in\mathrm{ssJSet}\,q\,\kappa$ with $a^{q^2}=a$, $a\neq 0$ and $a\neq 1728$; assume $q\ge 5$ and that the divisor $\sigma\cdot V-V$ (the action being through `arithmeticGalois` of the full level-$1\cdot q$ function field on divisors) has degree zero. Then there exists a degree-zero divisor $D$ on $\mathrm{modularFunctionFieldBar}(1\cdot q)$ such that: every place in the support of $D$ is strict of the first or of the second kind for $P$; the gluing datum $P.\mathrm{glueData}$ of $D$ for the node pairs obtained from $W$ through `smulNodePairEmb` applied to the semilinear automorphism $\mathrm{arithFrobC}\,q\,\kappa\,1$, namely the triple consisting of the pushforward along $P.\mathrm{reduceFst}$ of the strict-first part of $D$, the pushforward along $P.\mathrm{reduceSnd}$ of the strict-second part of $D$, and the trivial unit component, is admissible, i.e. both divisor components have degree zero and, for every pair $s$ in that finset, the first component vanishes at $s.1$ and the second at $s.2$; and the class of $D$ in $\mathrm{Pic}^0$ equals the class of $\sigma\cdot V-V$.
--
--   This is the class-representative step in the analysis of the displacement $\sigma V - V$ by inertia at an annulus point of the level-$q$ modular curve, where the point reduces to a supersingular crossing of the special fibre carrying no extra automorphisms ($a\neq 0,1728$): the class is moved to a divisor supported only at strict places and normalised so that its two pushforwards form an admissible gluing datum. It feeds [`ModularCurve.PlaceSpecialization.exists_goodRep_gluedMk_eq_nodeUnit_smul_single_sub_self_levelOne`](thm.html#ModularCurve.PlaceSpecialization.exists_goodRep_gluedMk_eq_nodeUnit_smul_single_sub_self_levelOne), which computes the resulting class in the glued Picard group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_goodRep_admissible_smul_single_sub_self_of_ne_zero_of_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_goodRep_admissible_smul_single_sub_self_of_ne_zero_of_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hval : LevelOneProlongationPair.NodeValueLaw q (IsLocalRing.residue A))
    (S₀ : Finset (ResidueField A)) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q (ResidueField A))
    (hNR : R.RegularityLaw S₀)
    (W : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 (ResidueField A))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hV₁ : ¬ P.IsStrictFst V) (hV₂ : ¬ P.IsStrictSnd V) (hVW : P.reduceFst V ∈ W)
    (a : ResidueField A) (ha : a ∈ ssJSet q (ResidueField A)) (ha2 : a ^ (q ^ 2) = a)
    (hVa : P.reduceFst V = (frobNodePair q a).1)
    (hq5 : 5 ≤ q) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (hdeg : arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1
        ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))) :
    ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (1 * q))))),
      P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) ∧
      P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) 1) W)
          (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
        ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) 1) W) ∧
      Pic0.mk D = Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1, hdeg⟩ := by sorry
