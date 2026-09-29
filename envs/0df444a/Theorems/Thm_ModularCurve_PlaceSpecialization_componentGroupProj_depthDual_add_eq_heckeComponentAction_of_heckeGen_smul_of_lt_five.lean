-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five
-- name    : ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/ceeaf0cc-39c9-5729-a540-be63aa3dee00
-- title:
--   Hecke transport of depth functionals in component groups, q<5
-- statement:
--   Fix $N\ge 1$ and a prime $q$ with $q\nmid N$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, so that the residue field $\kappa=\mathrm{ResidueField}\,A$ has characteristic $q$. Assume given: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,\kappa\,N$ consisting exactly of the supersingular places `ssPlaces q N κ`; modular polynomial data for $q$ (a monic bivariate $\Phi$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$) satisfying the Kronecker congruence $\Phi \equiv (X^q-Y)(X-Y^q)$ modulo $q$; integrality of the two level-raising inclusions $\alpha,\beta$ from level $N$ to level $Nq$ over $\overline{\mathbb Q}$; a place-specialisation datum $P$ for $A$, $q$, $N$ with residue map $\mathrm{residue}_A$; a prolongation tuple $R$ for $P$ which is a model, satisfies the fixed-place order law and the regularity law along $W$; a width function $e$ agreeing with $\mathrm{placeWidthChar}\,q\,N$ on $W$; and a function $\mathrm{depth}$ on the places of $\mathrm{modularFunctionFieldBar}(Nq)$ such that at each $w\in W$ there are a number field $K\subset\overline{\mathbb Q}$, an element of the coefficient ring $A\cap K$ reducing to $w(j)$, a generator $\varpi$ of the kernel of reduction with $q=\varpi^{e_K}\varepsilon$ for a unit $\varepsilon$, divisibility of residues of positive order by residues of order one at $w$ and at $\mathrm{arithFrobC}\,q\,\kappa\,N\cdot w$, and node coordinates $c$ over $K$ at $w$ with $c.x\,c.y=\mathrm{nodeConst}(\varpi)^{E}u$ for some $E$ and unit $u$, satisfying the depth value law for $\mathrm{depth}$. Assume further a prime $\ell\nmid Nq$ and an integer matrix $B$ indexed by the glued node pairs $\mathrm{nodePairsOfPlaces}(\mathrm{arithFrobC}\,q\,\kappa\,N)\,W$ whose entries $B\,t\,s$ are, whenever the degeneracy roof at $\ell$ over $\kappa$ has principal divisors and the two characteristic-$q$ degeneracy maps at $\ell$ are integral, the coefficients at $s$ of the divisor correspondence of $\mathrm{heckeAlphaC}$, $\mathrm{heckeBetaC}$ applied to the single divisor at $t$; assume the row sums of $B$ equal $\ell+1$ and the symmetry $e_j B_{ij}=e_i B_{ji}$ for the widths $\mathrm{widthOfPlaces}$. Let finally $D,D'$ be degree-zero divisors on $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$, each supported on places that are fixed by the inertia subgroup of $A$ over $\mathbb Q$ acting through $\mathrm{arithmeticGalois}$ and are strictly of the first kind, strictly of the second kind, or whose first reduction lies in $W$, with $\mathrm{heckeGen}\,\ell\cdot[D]=[D']$ in $JZero(Nq)$ for the Hecke module structure $\mathrm{heckeModuleBar}$; let $s_0$ be a glued node pair; and assume $q<5$. Then, writing $F(X)=P.\mathrm{depthDual}\,\mathrm{depth}\,X+\deg(P.\mathrm{sndDiv}\,X)\cdot\bigl(e(s_{0,1})\,\mathrm{crossingCoord}\,s_0\bigr)$, the class of $F(D')$ in the component group of the widths $\mathrm{widthOfPlaces}$ equals the image of the class of $F(D)$ under $\mathrm{heckeComponentAction}$ for $B$.
--
--   This is the Hecke equivariance, on the component group attached to the supersingular node widths of $X_0(Nq)$ in characteristic $q$, of the depth functional attached to a degree-zero divisor, in the small residue characteristic case $q<5$ where the widths at $j=0$ are wild. It is combined with the complementary branches to yield the unrestricted statement [`ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul`](thm.html#ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul), which feeds the Hecke analysis of the component group used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five.lean

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five
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
      (hreg : R.RegularityLaw W)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (he : ∀ w ∈ W, e w = placeWidthChar q N w)
      (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
      (hdepth :
        (∀ w ∈ W, ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
          (xw : ↥(NodeLocalized.coeffSubring A K))
          (_ : NodeLocalized.redRestrict (IsLocalRing.residue A) K xw = w.evalAt (jGeomGen (ResidueField A) N))
          (ϖ : ↥(NodeLocalized.coeffSubring A K))
          (_ : ∀ d : ↥(NodeLocalized.coeffSubring A K),
            NodeLocalized.redRestrict (IsLocalRing.residue A) K d = 0 ↔ ∃ d', d = ϖ * d')
          (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (_ : IsUnit ε)
          (_ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
          (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (_ : IsUnit u)
          (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
            0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
            ∃ b : ↥(R.nodeIntegersOver K w),
              R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
          (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
            0 < (arithFrobC q (ResidueField A) N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
            (arithFrobC q (ResidueField A) N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
            ∃ b : ↥(R.nodeIntegersOver K w),
              R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩),
          c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧ c.DepthValueLaw depth))
      (ℓ : Nat.Primes) (hℓ : ¬ (ℓ : ℕ) ∣ N * q)
      (B : Matrix ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ℤ)
      (hB : haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
        ∀ [HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ)]
          (hαc : HeckeAlphaCIntegral (ResidueField A) N ℓ) (hβc : HeckeBetaCIntegral (ResidueField A) N ℓ)
          (s t : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
          B t s = Divisor.correspondence (heckeAlphaC (ResidueField A) N ℓ) (heckeBetaC (ResidueField A) N ℓ) hαc hβc
            (Finsupp.single t.1.1 1) s.1.1)
      (hrow : HeckeRowSums B (((ℓ : ℕ) : ℤ) + 1))
      (hsym : HeckeWeightSymm (widthOfPlaces (arithFrobC q (ResidueField A) N) W e) B)
      (D D' : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
      (hD : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ,
            arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
          (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W))
      (hD' : ∀ V ∈ (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ,
            arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
          (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W))
      (hT :
        (letI := heckeModuleBar (N * q); heckeGen ℓ • (Pic0.mk D : JZero (N * q))) = Pic0.mk D')
      (s₀ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) ×
        Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
      (hs₀ : s₀ ∈ nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
      (hq5 : q < 5),
      componentGroupProj (widthOfPlaces (arithFrobC q (ResidueField A) N) W e)
          (P.depthDual (arithFrobC q (ResidueField A) N) W depth
              (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) +
            Divisor.degree (P.sndDiv (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) •
              ((e s₀.1 : ℤ) • crossingCoord
                (⟨s₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)))) =
        heckeComponentAction (widthOfPlaces (arithFrobC q (ResidueField A) N) W e) B hrow hsym
          (componentGroupProj (widthOfPlaces (arithFrobC q (ResidueField A) N) W e)
            (P.depthDual (arithFrobC q (ResidueField A) N) W depth
                (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) +
              Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) •
                ((e s₀.1 : ℤ) • crossingCoord
                  (⟨s₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))))) := by sorry
