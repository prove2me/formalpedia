-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/9b0e7fb9-962a-525e-8eea-fbe549789d79
-- title:
--   Component charts and a doubly attached annulus at j∈{0,1728}
-- statement:
--   Fix a prime $q\ge 5$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red:A\to k$ whose kernel is the maximal ideal of $A$; fix a modular-polynomial datum `data` for $q$ satisfying the Kronecker congruence $\Phi\equiv (Y^{q}-X)(Y-X^{q})$ mod $q$, integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of level $1$ into level $1\cdot q$ over $\overline{\mathbb Q}$, and a place specialisation $P$ for these data. Let $W$ be a finite set of places of `modularFunctionFieldC k 1` whose members are exactly the supersingular places (rational, with $j$ and $j_N$ regular, and supersingular $j$-value), and let $R$ be a prolongation tuple for $P$: it carries $\overline{red}:\kappa_A\to k$ lifting $red$, a map $\iota$ of full modular function fields, and two regular prolongations $R.R_1$, $R.R_2$ of $A$ to $\overline{F}_{1\cdot q}:=$ `modularFunctionFieldBar (1 * q)`, the second obtained from the first through the Atkin–Lehner involution. Assume `R.IsModel` (the two divisor laws and the two cusp laws), the regularity and node-value laws for $W$, and `OrderLawFixed`. Let $K\subset\overline{\mathbb Q}$ be a number field, $w\in W$ a place satisfying `R.ValueIntegralityLaw w` (every $f$ in the node ring at $w$ has $V$-value in $A$ for all $V$ with $P.\mathrm{reduceFst}\,V=w$), and suppose $w(j)=0$ or $w(j)=1728$. Let $\varpi$ generate the kernel of $red$ restricted to $A\cap K$, let $e_K\ge1$ and $\varepsilon$ a unit with $q=\varpi^{e_K}\varepsilon$, and let $c=(x,y)$ be node coordinates over $K$ at $w$ (so $x$ has first residue $0$ and second residue of order $1$ at the Frobenius twist $\varphi\cdot w$, and $y$ has second residue $0$ and first residue of order $1$ at $w$) together with $e_w\ge1$ and a unit $u$ of the node ring over $K$ at $w$ such that $xy=\varpi^{e_we_K}u$, the ideal $(\varpi,x,y)$ is maximal and is the only maximal ideal, $(\varpi,x)$ and $(\varpi,y)$ are prime with $y\notin(\varpi,x)$ and $x\notin(\varpi,y)$, the node ring is Noetherian, and every element of it differs from the image of a constant by a non-unit. Let $\mu$ be an absolute value on $\overline{\mathbb Q}$ with $A=\{\mu\le1\}$. Then, regarding `modularFunctionFieldC k 1` as a $\kappa_A$-algebra through $\overline{red}$, there are component charts $C_1,C_2$ of $\overline F_{1\cdot q}$ with values in `modularFunctionFieldC k 1`, places $x_1,x_2$ of the latter over $\kappa_A$, and annuli $An_1,An_2$ over $A$ in $\overline F_{1\cdot q}$ such that: the two annuli have the same domain and the same non-zero modulus $\pi$, with $An_2.\mathrm{param}\cdot An_1.\mathrm{param}=\pi$; $An_1$ is attached to $C_1$ at $x_1$ and $An_2$ to $C_2$ at $x_2$; the annulus is wide, i.e. two places of its domain give different values of $\mu$ on the parameter; the integers of $C_1$ and $C_2$ coincide with those of $R.R_1$ and $R.R_2$; for $f$ in these integers, $C_i$-residue vanishes exactly when the corresponding $R.R_i$-residue does, and $x_1.\mathrm{ord}$ of the $C_1$-residue equals $w.\mathrm{ord}$ of $R.\mathrm{residue}_1(f)$ while $x_2.\mathrm{ord}$ of the $C_2$-residue equals the order of $R.\mathrm{residue}_2(f)$ at $\varphi\cdot w$; the domain of $An_1$ consists exactly of the places $V$ of $\overline F_{1\cdot q}$ with $P.\mathrm{reduceFst}\,V=w$ that are neither strict of the first kind nor of the second; on this domain $\mu(V(An_1.\mathrm{param}))=\mu(V(y))$; and $\mu(\pi)=\mu(q)^{e_w}$.
--
--   This is the special-centre case, $j=0$ or $j=1728$, of the construction of the supersingular annulus of $X_0(q)$ over $A$, presented as two mutually inverse readings of one annulus attached at its two ends to the charts carrying the Gauss prolongations $R.R_1$ and $R.R_2$, with the width of the annulus recorded by $\mu(\pi)=\mu(q)^{e_w}$. It is the hypothesis-heavy leaf used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel), which removes the restriction on the $j$-value.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728.lean

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

open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization
open ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_componentCharts_annuli_isAttached_of_isModel_of_eq_zero_or_eq_ofNat1728
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
    (hj : w.evalAt (jGeomGen k 1) = 0 ∨ w.evalAt (jGeomGen k 1) = 1728)
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
