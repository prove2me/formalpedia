-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/1861660a-1c71-5153-847e-7a8d435c7d6a
-- title:
--   Component charts and attached annuli at a supersingular node
-- statement:
--   Fix a prime $q\ge 5$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}:A\to k$ whose kernel is exactly the maximal ideal of $A$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two degeneracy maps $\bar\alpha,\bar\beta$ at level $1$, a place specialization $P$ for these data, and a prolongation tuple $R$ for $P$. It is assumed that $R$ is a model (the two divisor laws and the two cusp laws hold), that $R$ satisfies the regularity law and the node-value law relative to a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\ k\ 1$ consisting precisely of the supersingular places $\mathrm{ssPlaces}\ q\ 1\ k$, and that $R$ satisfies `OrderLawFixed`. Further data: a number field $K\subset\overline{\mathbb Q}$; a place $w\in W$ for which $R$ satisfies the value-integrality law; an element $\varpi$ of the coefficient subring $A\cap K$ generating the kernel of $\mathrm{red}$ restricted to that subring (i.e. $\mathrm{red}\,d=0$ iff $\varpi\mid d$); integers $e_K\ge 1$ and a unit $\varepsilon$ of $A\cap K$ with $q=\varpi^{e_K}\varepsilon$; node coordinates $c$ at $w$ over $K$, i.e. elements $c.x,c.y$ of the ring $R.\mathrm{nodeIntegersOver}\ K\ w$ with $R$-residue$_1$ of $c.x$ zero, $\mathrm{ord}$ of residue$_2(c.x)$ equal to $1$ at the arithmetic-Frobenius translate $\varphi w$, residue$_2(c.y)$ zero and $\mathrm{ord}_w$ of residue$_1(c.y)$ equal to $1$; an integer $e_w\ge1$ and a unit $u$ with $c.x\,c.y=(\varpi)^{e_we_K}u$, where $\varpi$ is read in the node ring through $R.\mathrm{nodeConst}$; the hypotheses that $(\varpi,c.x,c.y)$ is maximal and is the only maximal ideal, that $(\varpi,c.x)$ and $(\varpi,c.y)$ are prime with $c.y\notin(\varpi,c.x)$ and $c.x\notin(\varpi,c.y)$, that the node ring is Noetherian, and that every element of it differs from some constant $R.\mathrm{nodeConst}\,o$ by a non-unit; finally an absolute value $\mu$ on $\overline{\mathbb Q}$ with $A=\{a:\mu(a)\le1\}$. Viewing $\mathrm{modularFunctionFieldC}\ k\ 1$ as an algebra over the residue field of $A$ via $R.\mathrm{redBar}$ followed by the structure map into the function field, the conclusion asserts the existence of two component charts $C_1,C_2$ for $A$ on $\mathrm{modularFunctionFieldBar}\ (1\cdot q)$ with residues in $\mathrm{modularFunctionFieldC}\ k\ 1$, two places $x_1,x_2$ of the latter over the residue field of $A$, and two annuli $\mathrm{An}_1,\mathrm{An}_2$ for $A$, such that: the two annuli have the same domain and the same modulus, that modulus is non-zero, and the product $\mathrm{An}_2.\mathrm{param}\cdot\mathrm{An}_1.\mathrm{param}$ equals the image of the modulus; $\mathrm{An}_1$ is attached to $(C_1,x_1)$ and $\mathrm{An}_2$ to $(C_2,x_2)$, meaning the node lies in the chart's node set, the parameter lies in the chart's integers with residue of order $1$ at the node, and for every chart integer with non-zero residue and vanishing order along the annulus the evaluation, corrected by the parameter to the power minus the order of the residue, is a unit of $A$; there are two places in $\mathrm{An}_1.\mathrm{dom}$ at which $\mu$ of the evaluated parameter differs; $C_1.\mathrm{integers}$ and $C_2.\mathrm{integers}$ coincide with the valuation subrings $R.R_1.\mathrm{integers}$ and $R.R_2.\mathrm{integers}$ respectively; for every element of these integers the chart residue is non-zero exactly when the corresponding $R$-residue is, and $\mathrm{ord}_{x_1}$ of the $C_1$-residue equals $\mathrm{ord}_w$ of $R.\mathrm{residue}_1$, while $\mathrm{ord}_{x_2}$ of the $C_2$-residue equals $\mathrm{ord}_{\varphi w}$ of $R.\mathrm{residue}_2$; $\mathrm{An}_1.\mathrm{dom}$ consists exactly of the places $V$ with $P.\mathrm{reduceFst}\,V=w$ that are neither strict of the first kind nor of the second; at each such $V$ one has $\mu(V(\mathrm{An}_1.\mathrm{param}))=\mu(V(c.y))$; and $\mu$ of the modulus equals $\mu(q)^{e_w}$.
--
--   This is the instantiation step translating the crossing presentation of the node ring at a supersingular place of $X_0(q)$ into the vocabulary of semistable charts: the two Gauss prolongations of the model tuple are realised as component charts, the places reducing to the node form the common domain of a pair of annuli attached at the two ends, with parameter product the modulus and $|\text{modulus}|=|q|^{e_w}$. It supplies the geometric input for the twisted-chord estimate [`ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_le_mul_prod_and_rigid_of_twist_levelOne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_le_mul_prod_and_rigid_of_twist_levelOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel
    {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W : Finset (Place k (modularFunctionFieldC k 1))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (hVI : R.ValueIntegralityLaw w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε)
    (c : R.NodeCoordinates K w) (ew : ℕ) (hew : 1 ≤ ew)
    (u : ↥(R.nodeIntegersOver K w)) (hu : IsUnit u)
    (hxy : c.x * c.y = R.nodeConst K w ϖ ^ (ew * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hbr : (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
        c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y})
    (hnoeth : IsNoetherianRing ↥(R.nodeIntegersOver K w))
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))

    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    letI : Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k 1) :=
      ((algebraMap k ↥(modularFunctionFieldC k 1)).comp R.redBar).toAlgebra
    ∃ (C₁ : ComponentChart A ↥(modularFunctionFieldBar (1 * q)) ↥(modularFunctionFieldC k 1)) (x₁ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k 1))
      (C₂ : ComponentChart A ↥(modularFunctionFieldBar (1 * q)) ↥(modularFunctionFieldC k 1)) (x₂ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC k 1))
      (An₁ An₂ : Annulus A ↥(modularFunctionFieldBar (1 * q))),

      An₂.dom = An₁.dom ∧ An₂.modulus = An₁.modulus ∧ ((An₁.modulus : AlgebraicClosure ℚ) ≠ 0) ∧
      An₂.param * An₁.param = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (An₁.modulus : AlgebraicClosure ℚ) ∧
      An₁.IsAttached C₁ x₁ ∧ An₂.IsAttached C₂ x₂ ∧
      (∃ Q₁ ∈ An₁.dom, ∃ Q₂ ∈ An₁.dom, μ (Q₁.evalAt An₁.param) ≠ μ (Q₂.evalAt An₁.param)) ∧

      (∀ f : ↥(modularFunctionFieldBar (1 * q)), f ∈ C₁.integers ↔ f ∈ R.R₁.integers) ∧ (∀ f : ↥(modularFunctionFieldBar (1 * q)), f ∈ C₂.integers ↔ f ∈ R.R₂.integers) ∧

      (∀ (f : ↥(modularFunctionFieldBar (1 * q))) (hC : f ∈ C₁.integers) (h₁ : f ∈ R.R₁.integers),
        (C₁.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₁.residue ⟨f, h₁⟩ ≠ 0) ∧
        x₁.ord (C₁.residue ⟨f, hC⟩) = w.ord (R.residue₁ ⟨f, h₁⟩)) ∧
      (∀ (f : ↥(modularFunctionFieldBar (1 * q))) (hC : f ∈ C₂.integers) (h₂ : f ∈ R.R₂.integers),
        (C₂.residue ⟨f, hC⟩ ≠ 0 ↔ R.R₂.residue ⟨f, h₂⟩ ≠ 0) ∧
        x₂.ord (C₂.residue ⟨f, hC⟩) = (arithFrobC q k 1 • w).ord (R.residue₂ ⟨f, h₂⟩)) ∧

      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), V ∈ An₁.dom ↔ (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)) ∧

      (∀ V ∈ An₁.dom, μ (V.evalAt An₁.param) = μ (V.evalAt (c.y : ↥(modularFunctionFieldBar (1 * q))))) ∧

      μ (An₁.modulus : AlgebraicClosure ℚ) = μ ((q : ℕ) : AlgebraicClosure ℚ) ^ ew := by sorry
