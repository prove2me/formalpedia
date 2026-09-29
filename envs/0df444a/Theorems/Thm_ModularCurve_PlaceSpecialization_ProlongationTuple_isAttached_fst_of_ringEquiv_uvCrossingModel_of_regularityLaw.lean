-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isAttached_fst_of_ringEquiv_uvCrossingModel_of_regularityLaw
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.isAttached_fst_of_ringEquiv_uvCrossingModel_of_regularityLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/7978b907-c32b-58e9-b437-5792c146de24
-- title:
--   Attachment of the node annulus to the first component chart
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N \neq 0$, a field $k$ of characteristic $q$ which is algebraically closed, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence $hKr$, integrality of the two degeneracy maps $h\alpha, h\beta$, a place specialisation $P$ of $X_0(N)$ over these, and a prolongation tuple $R$ for $P$. Assume $q \nmid N$, that $R$ is a model (the two divisor laws and the two cusp laws), that $R$ satisfies the fixed-order law, and fix a number field $K \subseteq \overline{\mathbb Q}$, a place $w$ of `modularFunctionFieldC k N` which is supersingular (rational, affine-geometric, with $j$-value in the supersingular set), the value-integrality law of $R$ at $w$, a finite set $W_0$ of places with $w \in W_0$ on which $R$ satisfies the regularity law, and the hypothesis that every element of the node ring $R.\mathrm{nodeIntegersOver}\,K\,w$ differs from some constant $R.\mathrm{nodeConst}\,K\,w\,o$ by a non-unit, this node ring being local and noetherian. Fix $\varpi$ in $A \cap K$ generating the kernel of the reduction $A \cap K \to k$ in the sense that $d$ reduces to $0$ iff $\varpi \mid d$; a complete discrete valuation domain $W$ with irreducible $\pi$, a ring homomorphism $\sigma$ from $W$ to the adic completion of the node ring with $\sigma(\pi)$ the image of $R.\mathrm{nodeConst}\,K\,w\,\varpi$, an exponent $E \geq 1$, and a ring isomorphism $\iota$ of that completion with the crossing model $W[[U,V]]/(UV - \pi^{E})$ carrying $\sigma(o)$ to the constant $o$, such that branch orders are read off as follows: if $f$ in the node ring has nonvanishing first node residue of order $n$ at $w$, then $\iota(f) - \gamma V^{n}$ lies in $(\pi, U)$ for some unit $\gamma$, and symmetrically, with $U$ and $V$ interchanged, for the second node residue and its order at $\mathrm{arithFrob}\cdot w$. Fix node coordinates $c = (c.x, c.y)$ at $(K, w)$, an exponent $E_0$ and a unit $u$ with $c.x\,c.y = (R.\mathrm{nodeConst}\,K\,w\,\varpi)^{E_0} u$, and assume the first node residue of $c.y$ is nonzero of order $1$ at $w$. Finally let $An$ be an annulus over $A$ in `modularFunctionFieldBar (N * q)` whose domain consists exactly of the places $V'$ with $P.\mathrm{reduceFst}\,V' = w$ that are neither strict of the first kind nor strict of the second kind, whose parameter is $c.y$ and whose modulus is $\varpi^{E_0}$. Give `modularFunctionFieldC k N` its algebra structure over the residue field of $A$ via $R.\mathrm{redBar}$ followed by $k \to$ `modularFunctionFieldC k N`. Then for every component chart $C_1$ over $A$ on `modularFunctionFieldBar (N * q)` with values in `modularFunctionFieldC k N` and every place $x_1$ of the latter over the residue field of $A$ with $x_1 \in C_1.\mathrm{nodes}$, if the valuation ring of $C_1$ has the same elements as $R.R_1.\mathrm{integers}$, and if for every such element the residue of $C_1$ vanishes exactly when the first residue of $R$ does, with $x_1.\mathrm{ord}$ of the former equal to $w.\mathrm{ord}$ of the latter, then $An$ is attached to $C_1$ at $x_1$: $x_1$ is a node of $C_1$, the parameter $c.y$ lies in $C_1.\mathrm{integers}$ with residue of order $1$ at $x_1$, and for every $f \in C_1.\mathrm{integers}$ with nonvanishing residue and $\mathrm{ord}_{P'} f = 0$ at all $P'$ in the domain of $An$, the value $P'.\mathrm{evalAt}(f) \cdot P'.\mathrm{evalAt}(c.y)^{-x_1.\mathrm{ord}(C_1.\mathrm{residue}\,f)}$ lies in $A$ and is a unit there.
--
--   This is the first-branch end-attachment step in the semistable description of $X_0(Nq)$ in characteristic $q$: given a crossing presentation of the completed local ring at a supersingular node as $W[[U,V]]/(UV-\pi^{E})$, the annulus cut out by the node coordinate $c.y$ is shown to be attached, in the sense of the annulus/component-chart formalism, to the chart whose valuation ring is the first Gauss prolongation. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_crossingPresentation`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_crossingPresentation), which assembles charts and annuli into the glued special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isAttached_fst_of_ringEquiv_uvCrossingModel_of_regularityLaw.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.isAttached_fst_of_ringEquiv_uvCrossingModel_of_regularityLaw
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (hord : R.OrderLawFixed)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hvalA : R.ValueIntegralityLaw w)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hwW₀ : w ∈ W₀) (hreg : R.RegularityLaw W₀)
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w))
    (hσπ : σ π = algebraMap _ _ (R.nodeConst K w ϖ))
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₁ w ⟨f, f.2.1⟩ ≠ 0 →
          w.ord (R.nodeResidue₁ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥(R.nodeIntegersOver K w)) (n : ℕ), R.nodeResidue₂ w ⟨f, f.2.1⟩ ≠ 0 →
          (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨f, f.2.1⟩) = (n : ℤ) →
          ∃ γ, IsUnit γ ∧ ι (algebraMap _ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (c : R.NodeCoordinates K w) (E₀ : ℕ) (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ E₀ * u)
    (hy₁ : R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ ≠ 0 ∧ w.ord (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩) = 1)
    (An : Annulus A ↥(modularFunctionFieldBar (N * q)))
    (hdom : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V' ∈ An.dom ↔ (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V'))
    (hparam : An.param = (↑c.y : ↥(modularFunctionFieldBar (N * q)))) (hmod : (An.modulus : AlgebraicClosure ℚ) = (ϖ : AlgebraicClosure ℚ) ^ E₀) :
    letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N) :=
      ((algebraMap k ↥(modularFunctionFieldC k N)).comp R.redBar).toAlgebra
    ∀ (C₁ : ComponentChart A ↥(modularFunctionFieldBar (N * q)) ↥(modularFunctionFieldC k N)) (x₁ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k N)),
      x₁ ∈ C₁.nodes →
      (∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ C₁.integers ↔ f ∈ R.R₁.integers) →
      (∀ (f : ↥(modularFunctionFieldBar (N * q))) (hC : f ∈ C₁.integers) (h₁ : f ∈ R.R₁.integers),
        (C₁.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₁.residue ⟨f, h₁⟩ ≠ 0) ∧
        x₁.ord (C₁.residue ⟨f, hC⟩) = w.ord (R.residue₁ ⟨f, h₁⟩)) →
      An.IsAttached C₁ x₁ := by sorry
