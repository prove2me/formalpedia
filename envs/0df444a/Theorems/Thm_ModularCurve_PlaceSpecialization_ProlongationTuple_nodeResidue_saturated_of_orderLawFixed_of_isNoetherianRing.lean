-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_orderLawFixed_of_isNoetherianRing
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_saturated_of_orderLawFixed_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/92f0427e-0468-5b81-be12-62a1f0c129ae
-- title:
--   Saturation of the two node residue maps at a supersingular node
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a natural number $N \neq 0$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \bmod q$, together with the integrality of the two Hecke ring homomorphisms $\bar\alpha$, $\bar\beta$ at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$, and a place specialization $P$ of these data. Let $R$ be a prolongation tuple for $P$, and assume $q \nmid N$, that $R$ satisfies `IsModel` (the two divisor laws and the cusp laws at $\infty$ and at $0$) and `OrderLawFixed` (the order of a reduction splits as $\mathrm{ord}_v$ of the first residue plus $\mathrm{ord}$ at the geometric Frobenius translate of $v$ of the second residue, at affine places fixed by the square of Frobenius). Let $W$ be a finite set of places of the geometric modular function field $\mathrm{modularFunctionFieldC}\,k\,N$, all supersingular (lying in $\mathrm{ssPlaces}\,q\,N\,k$), and assume $R$ satisfies `RegularityLaw W` and `NodeValueLaw W`. Let $K$ be a finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ and $w \in W$, and suppose the node ring $R.\mathrm{nodeIntegersOver}\,K\,w$ — the subring of $f$ in $R.\mathrm{nodeIntegers}\,w$ whose Laurent series lies in $\mathrm{NodeLocalized.fieldOver}\,(Nq)\,K$ — is local and noetherian. Then both residue maps of this ring are saturated: for $g, g'$ in it with $\mathrm{ord}_w(\mathrm{nodeResidue}_1\,g) > 0$ and $\mathrm{ord}_w(\mathrm{nodeResidue}_1\,g') = 1$ there is $b$ in it with $\mathrm{nodeResidue}_1\,g = \mathrm{nodeResidue}_1\,g' \cdot \mathrm{nodeResidue}_1\,b$; and likewise for $\mathrm{nodeResidue}_2$ and the order at the place $\mathrm{arithFrobC}\,q\,k\,N \cdot w$, the translate of $w$ by the coefficientwise arithmetic Frobenius automorphism.
--
--   This is a divisibility (saturation) property of the two branch residue maps at a supersingular node of the reduction of $X_0(Nq)$ in characteristic $q$: each branch order function takes the value of a uniformiser to the value of any element of positive order, up to a factor coming from the node ring itself. It feeds the analysis of the completed local ring at a supersingular point, being used in the construction of the annulus datum over a node package and in the identification of the completion of the node ring with a crossing model $k[[u,v]]/(uv - \pi^e)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_orderLawFixed_of_isNoetherianRing.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_saturated_of_orderLawFixed_of_isNoetherianRing
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)] :
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩) ∧
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩) := by sorry
