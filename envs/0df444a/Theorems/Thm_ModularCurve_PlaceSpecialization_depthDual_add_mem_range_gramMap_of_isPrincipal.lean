-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_depthDual_add_mem_range_gramMap_of_isPrincipal
-- name    : ModularCurve.PlaceSpecialization.depthDual_add_mem_range_gramMap_of_isPrincipal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/353230d8-e044-5526-96bb-90234549b2f9
-- title:
--   Depth functional of a principal divisor lies in the Gram image
-- statement:
--   Let $N\ge 1$, let $q\ge 5$ be a prime with $q\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, so that $k=\mathrm{ResidueField}\,A$ has characteristic $q$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\ k\ N$ whose members are exactly the supersingular places `ssPlaces q N k`; let `data` be a modular polynomial datum for $q$ (a monic $\Phi$ of degree $\psi(q)$ annihilating the $q$-expansions) satisfying the Kronecker congruence $\Phi\equiv(Y^q-X)(Y-X^q)$ mod $q$; let $h\alpha,h\beta$ be the integrality of the two degeneracy maps from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$; let $P$ be a `PlaceSpecialization` of $A$ at $q$ for this datum with reduction $\mathrm{res}_A$, and $R$ a prolongation tuple over $P$ satisfying the model law (the two divisor laws and the cusp laws at $\infty$ and $0$), the order law at the places fixed by the square of the geometric Frobenius, and the regularity and node-value laws on $W$. Suppose further that for each $w\in W$ there are: a number field $K_w\subset\overline{\mathbb{Q}}$, node coordinates $c_w=(x_w,y_w)$ over $K_w$ at $w$, an element $\varpi_w$ of the coefficient ring $A\cap K_w$ whose multiples are exactly the kernel of reduction on that ring, the value-integrality law at $w$, and a crossing presentation $x_wy_w=\mathrm{nodeConst}(\varpi_w)^E u$ with $E\ge1$ and $u$ a unit of the node ring over $K_w$. Let $e'>0$, let $D$ be a divisor of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$ that is principal, each place $V$ in whose support is strict of the first kind, strict of the second kind, or has $P.\mathrm{reduceFst}\,V\in W$, and let $\mathrm{depth}$ be a natural-valued weight on places such that for $w\in W$ and $V$ in the support of $D$ with $P.\mathrm{reduceFst}\,V=w$ one has $(c_w).\mathrm{yDepth}\,V^{\,e'}=v_A(q)^{\mathrm{depth}\,V}$ in the value group of $A$. Finally let $s_0$ be a pair of places lying in $\mathrm{nodePairsOfPlaces}(\mathrm{arithFrobC}\,q\,k\,N)\,W$, that is of the form $(w,\mathrm{Frob}\cdot w)$ with $w\in W$. Then the functional $P.\mathrm{depthDual}$ of $\mathrm{arithFrobC}$, $W$, $\mathrm{depth}$ and $D$ — the sum over node pairs $s$ of the coefficient at $s_1$ of the depth-weighted pushforward $\sum_V D(V)\,\mathrm{depth}(V)\,[P.\mathrm{reduceFst}\,V]$ times the coordinate functional at $s$ — plus $\deg(P.\mathrm{sndDiv}\,D)$ times $e'\cdot\mathrm{placeWidth}\,N\,(s_0)_1$ times the coordinate functional at $s_0$, lies in the image of the Gram map on the character lattice (the kernel of the degree map on functions on node pairs) associated with the widths $s\mapsto e'\cdot\mathrm{placeWidth}\,N\,s_1$.
--
--   This is the arithmetic input to the computation of the component group of the Jacobian of $X_0(Nq)$ in characteristic $q$: it says that the depth functional attached to a principal divisor of controlled support, corrected by a multiple of one crossing coordinate, is a period of the intersection (Gram) pairing of the node lattice, so that it dies in the cokernel presenting the component group. It is used in the identification of the Hecke action on that cokernel with the action on the depth classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_depthDual_add_mem_range_gramMap_of_isPrincipal.lean

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.depthDual_add_mem_range_gramMap_of_isPrincipal
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
        1 ≤ E ∧ IsUnit u ∧ (cs w).x * (cs w).y = R.nodeConst (Ks w) (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (ϖ w) ^ E * u)
      (e' : ℕ) (he' : 0 < e')
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      (hD : Divisor.IsPrincipal D)
      (hsupp : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
      (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
      (hdepth : ∀ (w : ↥W), ∀ V ∈ D.support,
        P.reduceFst V = (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) →
          (cs w).yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ depth V)
      (s₀ : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) ×
        Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))
      (hs₀ : s₀ ∈ nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W),
      P.depthDual (arithFrobC q (ResidueField A) N) W depth D +
          Divisor.degree (P.sndDiv D) •
            (((e' * placeWidth N s₀.1 : ℕ) : ℤ) •
              crossingCoord (⟨s₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))) ∈
        LinearMap.range
          (gramMap fun s : ↥(nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) =>
            e' * widthOfPlaces (arithFrobC q (ResidueField A) N) W (placeWidth N) s) := by sorry
