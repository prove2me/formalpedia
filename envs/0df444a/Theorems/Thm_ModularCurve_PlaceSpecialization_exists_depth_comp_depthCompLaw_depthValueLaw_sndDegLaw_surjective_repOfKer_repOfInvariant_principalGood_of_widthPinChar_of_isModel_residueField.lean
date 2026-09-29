-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel_residueField
-- name    : ModularCurve.PlaceSpecialization.exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/17beae89-f79e-580b-a1db-38edf338c761
-- title:
--   Depths and component map over the residue field of A
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$ whose residue field $k=\mathrm{ResidueField}\,A$ has characteristic $q$ and is algebraically closed, and $N\ge 1$ with $q\nmid N$; let `data` be modular polynomial data for $q$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$) satisfying the Kronecker congruence $\Phi \bmod q=(X^q-Y)(X-Y^q)$, and let $h\alpha,h\beta$ assert that the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$N$ into the level-$Nq$ function field over $\overline{\mathbb Q}$ are integral. Let $P$ be a place specialisation for $A,q,N$ relative to $k$ with its canonical residue map $A\to k$ (a map `sp` on places together with a map on $\mathrm{Pic}^0$ and the compatibility laws for the orders of $j$ and $j_N$), let $W$ be a finset of places of the geometric level-$N$ function field $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places `ssPlaces q N k`, and let $R$ be a prolongation tuple for $P$ which is a model (the two divisor laws and the two cusp laws), satisfies the regularity law and the node-value law at $W$, and satisfies the fixed-place order law. Finally let $e$ assign a natural number to each such place, with $e(w)=\mathrm{placeWidthChar}\,q\,N\,w=\mathrm{jWidthChar}\,q\,(w(j))/\mathrm{placeRamificationJ}\,N\,w$ for $w\in W$. Write $g=\mathrm{arithFrobC}\,q\,k\,N$ for the semilinear automorphism of the level-$N$ function field induced by the Frobenius of $k$, $S=\mathrm{nodePairsOfPlaces}\,g\,W$ for the set of pairs $(w,g\cdot w)$, $w\in W$, with widths $\mathrm{widthOfPlaces}\,g\,W\,e\colon s\mapsto e(s_1)$, and $\Phi(S,e)$ for the associated component group, the $\mathbb Z$-dual of the character lattice $\ker(\sum_{s}\mathrm{pr}_s)\subseteq \mathbb Z^S$ modulo the image of the Gram map of the widths. The assertion is that there exist a depth function $\mathrm{depth}$ on the places of $\mathrm{modularFunctionFieldBar}(Nq)$ and an additive map $\mathrm{comp}$ from the inertia invariants $\mathrm{inertiaInvariants}\,A\,(Nq)$ of $J^0=\mathrm{Pic}^0$ of that field (the classes fixed by the inertia subgroup of $A$ over $\mathbb Q$ acting through `arithmeticGalois`) to $\Phi(S,e)$ with eight properties: (i) the depth-comp law, i.e. for every degree-zero divisor $D$ whose class is inertia-invariant and whose support consists of inertia-fixed places each of which is strict of the first kind, strict of the second kind, or has first reduction in $W$, and every glued pair $s_0\in S$, $\mathrm{comp}$ of the class of $D$ is the image in $\Phi(S,e)$ of the depth functional of $D$ plus $\deg(P.\mathrm{sndDiv}\,D)$ times $e(s_{0,1})$ times the crossing coordinate of $s_0$; (ii) for every $w\in W$ there are a finite extension $K$ of $\mathbb Q$ inside $\overline{\mathbb Q}$, an element $x_w$ of the coefficient subring $A\cap K$ reducing to $w(j)$, an element $\varpi$ of that subring generating the kernel of reduction in the sense that $d$ reduces to $0$ iff $\varpi\mid d$, an exponent $e_K$ and a unit $\varepsilon$ with $q=\varpi^{e_K}\varepsilon$, node coordinates $c$ at $w$ over $K$, an exponent $E$, a unit $u$ of the node integers over $K$ at $w$, together with two hypotheses saying that the first and the second node residues of elements of positive order are divisible by those of order one, such that $c.x\,c.y=(\mathrm{nodeConst}\,K\,w\,\varpi)^E u$ and $c$ satisfies the depth-value law for $\mathrm{depth}$ (for each inertia-fixed place $V$ with first reduction $w$, the $y$-depth of $V$ equals the $A$-valuation of $q$ raised to $\mathrm{depth}\,V$); (iii) $e(w)>0$ for $w\in W$; (iv) for every inertia-invariant class of a degree-zero divisor $D$ all of whose support places are strict of the first or second kind, and every $s_0\in S$, $\mathrm{comp}$ of the class equals $\deg(P.\mathrm{sndDiv}\,D)$ times the class of the functional $e(s_{0,1})\cdot \mathrm{pr}_{s_0}$ restricted to the character lattice; (v) $\mathrm{comp}$ is surjective; (vi) every class in the kernel of $\mathrm{comp}$ is represented by a degree-zero divisor supported on strict places; (vii) every inertia-invariant class is represented by a degree-zero divisor whose support consists of inertia-fixed places each strict of the first kind, strict of the second kind, or with first reduction in $W$; and (viii) there is a principal divisor $G$ supported on strict places with $\deg(P.\mathrm{fstDiv}\,G)=m$ and $\deg(P.\mathrm{sndDiv}\,G)=-m$, where $m=\sum_{s\in S}\operatorname{lcm}_{s'}(e(s'_1))/e(s_1)$. Here strict of the first kind means that the Frobenius on geometric level-$N$ places carries the first reduction of the place to its second reduction while the square of the Frobenius moves the first reduction, and strict of the second kind is the mirror condition; $P.\mathrm{fstDiv}$, $P.\mathrm{sndDiv}$ are the restrictions of a divisor to the places of the respective kind.
--
--   This is the instance, for the canonical residue field $k=A/\mathfrak m$ of the valuation subring $A$ with its residue map, of the package describing the special fibre at $q$ of the Jacobian of the level-$Nq$ modular curve: depths of nodes, a surjective map from the inertia invariants to the component group of the two-component special fibre glued along the supersingular pairs, good representatives for kernel classes and for all invariant classes, and a principal divisor of bidegree $(m,-m)$. It is used by [`ModularCurve.DRModelPackageLevel.isGoodClass_of_extendsToPlace_pts`](thm.html#ModularCurve.DRModelPackageLevel.isGoodClass_of_extendsToPlace_pts) in the Deligne–Rapoport model package that underlies the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel_residueField.lean

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
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.PlaceSpecialization.exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel_residueField
    (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q] (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (W : Finset (Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (e : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N) → ℕ)
    (he : ∀ w ∈ W, e w = placeWidthChar q N w) :
    ∃ (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W e)),
      P.DepthCompLaw (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W e depth comp ∧
        (∀ w ∈ W, ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
          (xw : ↥(NodeLocalized.coeffSubring A K)) (_ : NodeLocalized.redRestrict (IsLocalRing.residue ↥A) K xw =
              w.evalAt (jGeomGen (IsLocalRing.ResidueField ↥A) N))
          (ϖ : ↥(NodeLocalized.coeffSubring A K))
          (_ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict (IsLocalRing.residue ↥A) K d = 0 ↔
              ∃ d', d = ϖ * d')
          (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (_ : IsUnit ε)
          (_ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
          (c : R.NodeCoordinates K w) (E : ℕ) (u : ↥(R.nodeIntegersOver K w)) (_ : IsUnit u)
          (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
            0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
            ∃ b : ↥(R.nodeIntegersOver K w),
              R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
          (_ : ∀ g g' : ↥(R.nodeIntegersOver K w),
            0 < (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
            (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
            ∃ b : ↥(R.nodeIntegersOver K w),
              R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩),
          c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧ c.DepthValueLaw depth) ∧
      (∀ w ∈ W, 0 < e w) ∧
      (∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := ↥(modularFunctionFieldBar (N * q)))))
          (hH : Pic0.mk D ∈ inertiaInvariants A (N * q)),
          P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) →
          ∀ s₀ : ↥(nodePairsOfPlaces (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W),
            comp ⟨Pic0.mk D, hH⟩ =
              (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).degree •
                componentGroupProj (widthOfPlaces (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W e)
                  ((widthOfPlaces (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W e s₀ : ℤ) •
                    (LinearMap.proj s₀ : (↥(nodePairsOfPlaces (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W) → ℤ)
                        →ₗ[ℤ] ℤ).comp
                      (characterLattice ↥(nodePairsOfPlaces (arithFrobC q (IsLocalRing.ResidueField ↥A) N)
                          W)).subtype)) ∧
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
          (P.fstDiv G).degree = ((∑ s : ↥(nodePairsOfPlaces (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W e) / widthOfPlaces
                (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W e s : ℕ) : ℤ) ∧
          (P.sndDiv G).degree = -((∑ s : ↥(nodePairsOfPlaces (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W),
            Finset.univ.lcm (widthOfPlaces (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W e) / widthOfPlaces
                (arithFrobC q (IsLocalRing.ResidueField ↥A) N) W e s : ℕ) : ℤ)) := by sorry
