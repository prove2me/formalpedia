-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul
-- name    : ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/00794f3c-56d1-558c-8e00-8cb8895776d2
-- title:
--   Hecke equivariance of the depth functional in the component group
-- statement:
--   Fix $N\ge 1$ and a prime $q$ with $q\nmid N$, and a valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$ (so the residue field $\kappa=\mathrm{ResidueField}\,A$ has characteristic $q$). Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,\kappa\,N$ whose members are exactly the supersingular places `ssPlaces q N κ`; let `data` be modular-polynomial data for $q$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$) satisfying the Kronecker congruence $\Phi \equiv (X^q-Y)(X-Y^q)$ mod $q$; let $h\alpha,h\beta$ assert integrality of the two degeneracy maps $\mathrm{heckeAlphaBar},\mathrm{heckeBetaBar}$ at level $N$ and prime $q$ over $\overline{\mathbb Q}$; let $P$ be a place specialisation of $A$ at $q$ in level $N$ with target $\kappa$ and reduction the residue map of $A$, and $R$ a prolongation tuple for $P$ which is a model (the two divisor laws and the cusp laws at $\infty$ and $0$), satisfies the fixed-place order law `OrderLawFixed` and the regularity law over $W$. Let $e$ be a width function agreeing with $\mathrm{placeWidthChar}\,q\,N$ on $W$, and let $\mathrm{depth}$ be a natural-number weight on the places of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ subject to the node-depth hypothesis: for every $w\in W$ there are a finite subextension $K/\mathbb Q$ of $\overline{\mathbb Q}$, an element of $A\cap K$ reducing to $w(\mathrm{jGeomGen})$, a uniformiser $\varpi$ of $A\cap K$ with $q=\varpi^{e_K}\varepsilon$ for a unit $\varepsilon$, node coordinates $c$ over $K$ at $w$, an exponent $E$ and a unit $u$ of the node integers over $K$ at $w$, together with two divisibility conditions on the orders of the first and second node residues (summarised here), such that $c.x\,c.y=\mathrm{nodeConst}(\varpi)^E u$ and $c$ obeys the depth-value law for $\mathrm{depth}$, i.e. the $y$-depth of each inertia-fixed place $V$ above $w$ is the valuation of $q$ raised to $\mathrm{depth}\,V$. Let $\ell$ be a prime with $\ell\nmid Nq$ and $B$ an integer matrix indexed by the node pairs $\{(w,\mathrm{arithFrobC}\,q\,\kappa\,N\cdot w):w\in W\}$ such that, assuming principal divisors on the characteristic-$\ell$ degeneracy roof over $\kappa$ and integrality of $\mathrm{heckeAlphaC},\mathrm{heckeBetaC}$, $B_{t,s}$ is the coefficient at the first place of $s$ of the push–pull correspondence applied to the divisor $1\cdot(\text{first place of }t)$; assume all row sums of $B$ equal $\ell+1$ and the weight symmetry $e_j B_{i j}=e_i B_{j i}$ for the widths $\mathrm{widthOfPlaces}$. Finally let $D,D'$ be degree-zero divisors on $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$ each of whose support places are fixed by the inertia subgroup of $A$ under the arithmetic Galois action and are strict of the first kind, strict of the second kind, or reduce under $P.\mathrm{reduceFst}$ into $W$, with $\mathrm{heckeGen}\,\ell$ carrying the class of $D$ in $\mathrm{JZero}(Nq)$ to the class of $D'$, and let $s_0$ be a node pair. Then, writing $F(D)=P.\mathrm{depthDual}(\mathrm{depth},D)+\deg(P.\mathrm{sndDiv}\,D)\cdot e(s_{0,1})\,\mathrm{crossingCoord}(s_0)$ for the associated functional on the character lattice of node pairs, the image of $F(D')$ under the projection to the component group of the widths equals $\mathrm{heckeComponentAction}$ of $B$ (with its row-sum and symmetry data) applied to the image of $F(D)$.
--
--   This is the Hecke-equivariance step in the computation of the component group of the special fibre at $q$ of the Jacobian of $X_0(Nq)$: it says that the depth functional attached to a degree-zero divisor, corrected by the degree of its strict second part, transforms under $T_\ell$ by the Brandt-type matrix $B$ on supersingular node pairs. It is used by the statement producing widths and a component map for the glued specialisation compatible with the characteristic-$q$ Hecke correspondence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul.lean

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

theorem
ModularCurve.PlaceSpecialization.componentGroupProj_depthDual_add_eq_heckeComponentAction_of_heckeGen_smul
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
      (hs₀ : s₀ ∈ nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W),
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
