-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_isTwistOf_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_laws
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_isTwistOf_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_laws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/682348aa-d48e-51b1-bef9-e48910764857
-- title:
--   Twist vector from a vanishing depth class in the component group
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbf{Q}}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$, a ring map $\mathrm{red} : A \to k$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two Hecke maps at level $Nq$, and a place specialisation $P$ of these data; assume $q \nmid N$. Let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k`, let $R$ be a prolongation tuple of $P$ satisfying `IsModel`, `RegularityLaw W`, `NodeValueLaw W` and `OrderLawFixed`, and let `dat` be a level-$N$ annulus datum for $R$ over $W$: coefficient fields $K_w \subseteq \overline{\mathbf{Q}}$, node coordinates $(x_w,y_w)$ over $K_w$ for $w \in W$, widths, a rational depth function $\delta$ on the places of `modularFunctionFieldBar (N*q)`, together with uniformisers, correction divisors and units. Assume: the width of each $w \in W$ is `placeWidthChar q N w`; for every $w \in W$ and every place $V$ with $P.\mathrm{reduceFst}\,V = w$ that is neither strict-first nor strict-second, $0 < \delta(V) < \mathrm{width}(w)$ and $(\mathrm{coord}\,w).\mathrm{yDepth}(V)^{\mathrm{den}\,\delta(V)} = v_A(q)^{\mathrm{num}\,\delta(V)}$; $\delta$ is invariant under the inertia subgroup of $A$ over $\mathbf{Q}$ acting through `arithmeticGalois`; each $K_w$ with $w \in W$ is fixed pointwise by that inertia subgroup, and every $K_w$ is finite-dimensional over $\mathbf{Q}$. Assume further chosen elements $\varpi_w$ of the coefficient subring $A \cap K_w$ generating the kernel of the reduction `NodeLocalized.redRestrict red` for $w \in W$, natural numbers $e_{K_w}$, and units $u_w$ of the node integers over $K_w$ at $w$ with $x_w y_w = \mathrm{nodeConst}(\varpi_w)^{\mathrm{width}(w)\,e_{K_w}} u_w$. Assume a second family: for each $w \in W$ an intermediate field $K'_w$ finite over $\mathbf{Q}$, node coordinates $c_w$ over $K'_w$ at $w$, an element $\varpi'_w$ of $A \cap K'_w$ generating the kernel of the corresponding reduction, the value-integrality law at $w$ (places over $w$ evaluate node integers into $A$), and an exponent $E \ge 1$ with $(c_w).x\,(c_w).y = \mathrm{nodeConst}(\varpi'_w)^{E}$ times a unit. Finally let $e' \ge 1$, let $D$ be a divisor on `modularFunctionFieldBar (N*q)` of degree $0$, invariant under the inertia subgroup, with support contained in the strict-first places, the strict-second places and the places reducing into $W$, and let $\mathrm{depth}$ be a natural-number-valued function on places such that $(c_w).\mathrm{yDepth}(V)^{e'} = v_A(q)^{\mathrm{depth}(V)}$ for $V$ in the support of $D$ with $P.\mathrm{reduceFst}\,V = w \in W$. Suppose that for every pair $s_0 \in \mathrm{nodePairsOfPlaces}(\mathrm{arithFrobC}\,q\,k\,N)\,W$ the class of $P.\mathrm{depthDual}$ of $(\mathrm{depth}, D)$ plus $\deg(P.\mathrm{sndDiv}\,D)$ times $e'\,\mathrm{placeWidthChar}\,q\,N\,(s_0)_1$ times the crossing coordinate at $s_0$ vanishes under `componentGroupProj` for the weights $s \mapsto e' \cdot \mathrm{widthOfPlaces}$. Then there exists a twist vector $a$ for $W$, consisting of integers $a_Z, a_{Z'}$ and integers $a_E(w,d)$, such that `dat.IsTwistOf a D` holds: the degree of the strict-first part of $D$ equals $-\sum_{w \in W}(\mathrm{endSlopeFst}\,a\,w + \mathrm{endShareFst}\,D\,w)$, the degree of the strict-second part equals $-\sum_{w \in W}(\mathrm{endSlopeSnd}\,a\,w + \mathrm{endShareSnd}\,D\,w)$, and for every $w \in W$ and every $d$ with $1 \le d$ and $d + 1 \le \mathrm{width}(w)$ the tent-weighted circle degree $\sum_{V} D(V)\max(0, 1 - |\delta(V) - d|)$, over the support of $D$ at $w$ away from the strict places, equals minus the second difference $\mathrm{chainVal}(a,w,d-1) - 2\,\mathrm{chainVal}(a,w,d) + \mathrm{chainVal}(a,w,d+1)$, where $\mathrm{chainVal}$ is $a_Z$ at $d = 0$, $a_{Z'}$ for $d \ge \mathrm{width}(w)$, and $a_E(w,d)$ otherwise.
--
--   This is the bookkeeping step that converts the vanishing of the fine depth class of an inertia-stable degree-zero divisor on $X_0(Nq)$ in the component group of the Néron model at $q$ — expressed through the intersection (Gram) pairing of the character lattice of the dual graph, subdivided at each supersingular point according to its width — into the existence of an integral twist vector whose discrete Laplacian reproduces the tent-weighted circle degrees and end orders of the divisor. It feeds the construction of a good divisor representing a prescribed class, in [`ModularCurve.PlaceSpecialization.exists_isGoodDiv_pic0Mk_eq_of_comp_eq_zero_of_depthCompLaw_depthValueLaw_repOfInvariant_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_isGoodDiv_pic0Mk_eq_of_comp_eq_zero_of_depthCompLaw_depthValueLaw_repOfInvariant_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumLevel_exists_isTwistOf_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_laws.lean

import Definitions.Def_ModularCurve_AnnulusSpecializationLevel
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumLevel.exists_isTwistOf_of_componentGroupProj_depthDual_eq_zero_of_inertiaStable_of_laws
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (dat : R.AnnulusDatumLevel W)
    (hwidthc : ∀ w ∈ W, dat.width w = placeWidthChar q N w)
    (hdepthQ : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
      (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      0 < dat.depthQ V ∧ dat.depthQ V < dat.width w ∧ (dat.coord w hw).yDepth V ^ (dat.depthQ V).den =
      A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ (dat.depthQ V).num.toNat)
    (hdepthσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      dat.depthQ (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = dat.depthQ V)
    (hKfix : ∀ w ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ dat.K w, σ z = z)
    (hK : ∀ w : Place k (modularFunctionFieldC k N), FiniteDimensional ℚ ↥(dat.K w))
    (ϖd : ∀ w : Place k (modularFunctionFieldC k N), ↥(NodeLocalized.coeffSubring A (dat.K w)))
    (hϖd : ∀ w ∈ W, ∀ d : ↥(NodeLocalized.coeffSubring A (dat.K w)),
      NodeLocalized.redRestrict red (dat.K w) d = 0 ↔ ∃ d', d = ϖd w * d')
    (eK : Place k (modularFunctionFieldC k N) → ℕ)
    (u : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ↥(R.nodeIntegersOver (dat.K w) w))
    (hu : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), IsUnit (u w hw) ∧
      (dat.coord w hw).x * (dat.coord w hw).y = R.nodeConst (dat.K w) w (ϖd w) ^ (dat.width w * eK w) * u w hw)
    (Ks : ↥W → IntermediateField ℚ (AlgebraicClosure ℚ)) [∀ w : ↥W, FiniteDimensional ℚ (Ks w)]
    (cs : ∀ w : ↥W, R.NodeCoordinates (Ks w) (w : Place k (modularFunctionFieldC k N)))
    (ϖ : ∀ w : ↥W, ↥(NodeLocalized.coeffSubring A (Ks w)))
    (hϖ : ∀ (w : ↥W) (d : ↥(NodeLocalized.coeffSubring A (Ks w))), NodeLocalized.redRestrict red (Ks w) d = 0 ↔ ∃ d', d = ϖ w * d')
    (hvalA : ∀ w : ↥W, R.ValueIntegralityLaw (w : Place k (modularFunctionFieldC k N)))
    (hxy : ∀ w : ↥W, ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver (Ks w) (w : Place k (modularFunctionFieldC k N)))),
      1 ≤ E ∧ IsUnit u ∧ (cs w).x * (cs w).y = R.nodeConst (Ks w) (w : Place k (modularFunctionFieldC k N)) (ϖ w) ^ E * u)
    (e' : ℕ) (he' : 0 < e')
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD0 : D.degree = 0)
    (hDstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • D = D)
    (hsupp : ∀ V ∈ D.support, P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)
    (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ)
    (hdepth : ∀ (w : ↥W), ∀ V ∈ D.support, P.reduceFst V = (w : Place k (modularFunctionFieldC k N)) →
      (cs w).yDepth V ^ e' = A.valuation (((q : ℕ) : AlgebraicClosure ℚ)) ^ depth V)
    (hread : ∀ (s₀ : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))
      (hs₀ : s₀ ∈ nodePairsOfPlaces (arithFrobC q k N) W),
      componentGroupProj
          (fun s : ↥(nodePairsOfPlaces (arithFrobC q k N) W) => e' * widthOfPlaces (arithFrobC q k N) W (placeWidthChar q N) s)
          (P.depthDual (arithFrobC q k N) W depth D +
            Divisor.degree (P.sndDiv D) • (((e' * placeWidthChar q N s₀.1 : ℕ) : ℤ) •
              crossingCoord (⟨s₀, hs₀⟩ : ↥(nodePairsOfPlaces (arithFrobC q k N) W)))) = 0) :
    ∃ a : ProlongationTuple.TwistVectorLevel (k := k) (N := N) W, dat.IsTwistOf a D := by sorry
