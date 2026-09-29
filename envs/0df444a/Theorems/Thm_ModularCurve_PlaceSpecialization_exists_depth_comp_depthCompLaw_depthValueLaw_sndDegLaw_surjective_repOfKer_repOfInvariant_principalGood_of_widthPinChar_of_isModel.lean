-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/64d854ea-7037-5318-ac1a-191341920c2b
-- title:
--   Depth function and surjective component map on inertia invariants
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb{Q}}$, $N$ a nonzero natural number, $k$ an algebraically closed field of characteristic $q$ and $\mathrm{red} : A \to k$ a ring homomorphism; let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence `hKr`, namely that the bivariate reduction of $\Phi$ modulo $q$ is $((CX)^q - X)\,(CX - X^q)$, and let `hα`, `hβ` assert that the Hecke maps $\bar\alpha,\bar\beta$ at level $N$ and $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Assume $q \nmid N$, and let $P$ be a place specialisation for these data (a map `sp` on places together with a map on degree-zero divisor classes and the compatibilities recorded in `PlaceSpecialization`). Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places `ssPlaces q N k`, let $R$ be a prolongation tuple for $P$ which is a model (the two divisor laws and the two cusp laws), satisfies the regularity law and the node-value law for $W$ and the fixed-place order law `OrderLawFixed`, and let $e$ be a width function on places agreeing on $W$ with `placeWidthChar q N`. Then there exist a depth function $\mathrm{depth}$ on the places of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$ and an additive map $\mathrm{comp}$ from the inertia invariants $\mathrm{inertiaInvariants}\,A\,(Nq)$ inside $J^0(Nq)$ to the component group of the width function $\mathrm{widthOfPlaces}(\mathrm{arithFrob}_q,W,e)$ (the dual of the character lattice modulo the image of the Gram map) such that: (i) `DepthCompLaw` holds, i.e. for every degree-zero divisor $D$ whose class is inertia-invariant and all of whose support places are fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb{Q}$ and are each strict of the first kind, strict of the second kind, or have first reduction in $W$, and for every glued pair $s_0$, $\mathrm{comp}$ of the class of $D$ is the projection of the depth functional of $D$ plus $\deg(\mathrm{sndDiv}\,D)$ times $(e\,s_{0,1})\cdot\mathrm{crossingCoord}$; (ii) for each $w \in W$ there are a number field $K \subset \overline{\mathbb{Q}}$, an element $x_w$ of $A \cap K$ reducing to the value of the $j$-generator at $w$, an element $\varpi$ of $A \cap K$ generating the kernel of the reduction there, an exponent $e_K$ and a unit $\varepsilon$ with $q = \varpi^{e_K}\varepsilon$, node coordinates $c$ for $K$ and $w$, an exponent $E$ and a unit $u$ of the node integers over $K$ at $w$, such that both branch residue maps are saturated in the stated divisibility sense (for the first at $w$, for the second at $\mathrm{arithFrob}_q \cdot w$), $c.x\,c.y = (\varpi)^E u$ in the node integers, and $c$ satisfies `DepthValueLaw` for $\mathrm{depth}$, i.e. for every inertia-fixed place $V$ with first reduction $w$ the $y$-depth of $V$ is the $A$-valuation of $q$ raised to $\mathrm{depth}\,V$; (iii) $e\,w > 0$ for $w \in W$; (iv) for every degree-zero $D$ with inertia-invariant class which is a good divisor (every support place strict of the first or of the second kind) and every glued pair $s_0$, $\mathrm{comp}$ of the class equals $\deg(\mathrm{sndDiv}\,D)$ times the projection of the width at $s_0$ times the $s_0$-coordinate functional on the character lattice; (v) $\mathrm{comp}$ is surjective; (vi) every $x$ in the inertia invariants with $\mathrm{comp}\,x = 0$ is the class of a good degree-zero divisor; (vii) every $x$ in the inertia invariants is the class of a degree-zero divisor all of whose support places are inertia-fixed and each strict of the first kind, strict of the second kind, or with first reduction in $W$; and (viii) there is a principal good divisor $G$ with $\deg(\mathrm{fstDiv}\,G) = \sum_s \mathrm{lcm}(\text{widths})/\mathrm{width}(s)$ and $\deg(\mathrm{sndDiv}\,G)$ the negative of that sum.
--
--   This is the combinatorial heart of the description of the component group of the Jacobian $J_0(Nq)$ in characteristic $q$ on the inertia invariants: it packages the depth function at the supersingular nodes, explicit node coordinates with their uniformisers, and a surjective component map reading depths, together with divisor representatives for its kernel and for all invariant classes and a principal good divisor of prescribed branch degrees. It is used by the subsequent statements that compare this component map with the Hecke action and with the glued specialisation, en route to the level-lowering input at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N] (k : Type*) [Field k]
    [CharP k q] (red : A →+* k) (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (he : ∀ w ∈ W, e w = placeWidthChar q N w) :
    ∃ (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q k N) W e)),
      P.DepthCompLaw (arithFrobC q k N) W e depth comp ∧
        (∀ w ∈ W, ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
          (xw : ↥(NodeLocalized.coeffSubring A K)) (_ : NodeLocalized.redRestrict red K xw = w.evalAt (jGeomGen k N))
          (ϖ : ↥(NodeLocalized.coeffSubring A K))
          (_ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
          (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (_ : IsUnit ε)
          (_ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
          (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (_ : IsUnit u)
          (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
            0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
            ∃ b : ↥(R.nodeIntegersOver K w),
              R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
          (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
            0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
            (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
            ∃ b : ↥(R.nodeIntegersOver K w),
              R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩),
          c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧ c.DepthValueLaw depth) ∧
      (∀ w ∈ W, 0 < e w) ∧
      (∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))))
          (hH : Pic0.mk D ∈ inertiaInvariants A (N * q)),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
          ∀ s₀ : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            comp ⟨Pic0.mk D, hH⟩ =
              (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).degree •
                componentGroupProj (widthOfPlaces (arithFrobC q k N) W e)
                  ((widthOfPlaces (arithFrobC q k N) W e s₀ : ℤ) •
                    (LinearMap.proj s₀ : (↥(nodePairsOfPlaces (arithFrobC q k N) W) → ℤ) →ₗ[ℤ] ℤ).comp
                      (characterLattice ↥(nodePairsOfPlaces (arithFrobC q k N) W)).subtype)) ∧
      Function.Surjective comp ∧
      (∀ x : ↥(inertiaInvariants A (N * q)), comp x = 0 →
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) ∧
            Pic0.mk D = (x : JZero (N * q))) ∧
      (∀ x : ↥(inertiaInvariants A (N * q)),
        ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))),
          (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
            (∀ σ ∈ A.inertiaSubgroupIn ℚ,
                arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
              (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)) ∧
            Pic0.mk D = (x : JZero (N * q))) ∧
      (∃ G : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        Divisor.IsPrincipal G ∧ P.IsGoodDiv G ∧
          (P.fstDiv G).degree = ((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ) ∧
          (P.sndDiv G).degree = -((∑ s : ↥(nodePairsOfPlaces (arithFrobC q k N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q k N) W e) / widthOfPlaces (arithFrobC q k N) W e s : ℕ) : ℤ)) := by sorry
