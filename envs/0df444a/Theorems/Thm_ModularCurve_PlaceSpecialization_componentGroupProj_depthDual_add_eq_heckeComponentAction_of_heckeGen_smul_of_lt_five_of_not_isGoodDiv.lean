-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv
-- name    : ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/a1c2f746-3094-5db9-b9b4-6b044f1e8ac0
-- title:
--   Hecke transport of the depth functional: annulus case, q<5
-- statement:
--   Let $N\ge 1$ and let $q$ be a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, so that the residue field $\kappa=\operatorname{ResidueField} A$ has characteristic $q$. Fix: a finite set $W$ of places of $\operatorname{modularFunctionFieldC}\kappa\,N$ consisting exactly of the supersingular places `ssPlaces q N κ`; modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi\equiv(X^q-Y)(X-Y^q)$ mod $q$; integrality of the two degeneracy maps $\bar\alpha,\bar\beta$ at level $N$, $q$; a place specialisation $P$ of $A$ reducing places of $\operatorname{modularFunctionFieldBar}N$ to places over $\kappa$; a prolongation tuple $R$ for $P$ which is a model (the two divisor laws and the two cusp laws), satisfies the order law at fixed places and the regularity law along $W$; a width function $e$ with $e(w)=\operatorname{placeWidthChar}q\,N\,w$ for $w\in W$; and a function $\mathrm{depth}$ on places of $\operatorname{modularFunctionFieldBar}(Nq)$ subject to `hdepth`: for every $w\in W$ there are a number field $K\subset\overline{\mathbb Q}$, an element of the coefficient subring $A\cap K$ reducing to $w(\,j\,)$, a uniformiser $\varpi$ of that subring with $q=\varpi^{e_K}\varepsilon$ for a unit $\varepsilon$, node coordinates $c$ over $K$ at $w$, an exponent $E$ and a unit $u$ of $R.\mathrm{nodeIntegersOver}K\,w$ such that (granted two cofinality conditions on the orders of the first and second node residues) $c.x\,c.y=\mathrm{nodeConst}_K(\varpi)^E u$ and $c$ obeys the depth value law for $\mathrm{depth}$, i.e. $c.\mathrm{yDepth}(V)=|q|_A^{\mathrm{depth}(V)}$ for every inertia-fixed place $V$ with $P.\mathrm{reduceFst}V=w$. Fix further a prime $\ell\nmid Nq$; an integer matrix $B$ indexed by the glued pairs $\operatorname{nodePairsOfPlaces}(\operatorname{arithFrobC}q\,\kappa\,N)W$ whose entry $B_{t,s}$ is, whenever the degeneracy roof in characteristic $\ell$ has principal divisors and $\alpha_C,\beta_C$ are integral, the coefficient at $s$ of the correspondence $\beta_{C*}\alpha_C^{*}$ applied to the divisor $1\cdot t$; the row-sum hypothesis $\sum_j B_{ij}=\ell+1$ and the weighted symmetry $e_j B_{ij}=e_i B_{ji}$ for the weights $\operatorname{widthOfPlaces}$ attached to $e$. Finally let $D,D'$ be degree-zero divisors on $\operatorname{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ each of whose support points are fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb Q$ and are either strict of the first or second kind for $P$ or have $P.\mathrm{reduceFst}$ in $W$, with $[D']=\mathrm{heckeGen}\,\ell\cdot[D]$ in $J^0(Nq)$; let $s_0$ be a glued pair in $\operatorname{nodePairsOfPlaces}$; and assume $q<5$, that $D$ and $D'$ are not both good (not every support point strict), and that $e$ is not identically $1$ on $W$. Then, in the component group attached to the weights $\operatorname{widthOfPlaces}$, the class of $P.\mathrm{depthDual}(\mathrm{depth},D')+\deg(P.\mathrm{sndDiv}\,D')\cdot e(s_0{}_{,1})\,\mathrm{crossingCoord}(s_0)$ equals $\operatorname{heckeComponentAction}(B)$ applied to the class of the same expression formed from $D$.
--
--   This is the case of the transport of the depth functional under the $\ell$-th Hecke operator in which the divisors involved are allowed non-strict (annulus) support points, in residue characteristic $q\in\{2,3\}$ and with some supersingular width exceeding one. It feeds the statement [`ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five`](thm.html#ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five), where this case is combined with the good-divisor and unit-width cases to give the Hecke-equivariance of the depth functional on the component group of the special fibre at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv.lean

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

theorem ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul_of_lt_five_of_not_isGoodDiv
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
      (hq5 : q < 5)
      (hcase : ¬ (P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧ P.IsGoodDiv (D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))))
      (hwid : ¬ ∀ w ∈ W, e w = 1),
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
