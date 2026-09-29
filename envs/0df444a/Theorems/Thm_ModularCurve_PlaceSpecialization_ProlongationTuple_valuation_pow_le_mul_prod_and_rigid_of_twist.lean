-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_le_mul_prod_and_rigid_of_twist
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_le_mul_prod_and_rigid_of_twist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/96f60f57-0406-56ad-9db2-31ebb20e93ec
-- title:
--   Twisted chord bounds and rigidity at a supersingular crossing
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N\ge 1$ with $q\nmid N$, an algebraically closed field $k$ of characteristic $q$ and a ring map $\mathrm{red}:A\to k$ whose kernel is exactly the maximal ideal of $A$, modular polynomial data for $q$ satisfying the Kronecker congruence $\Phi\equiv(Y^q-X)(Y-X^q)$ mod $q$, integrality of the two degeneracy inclusions $\bar\alpha,\bar\beta$, and a place specialization $P$ of the places of $\overline{\mathbb{Q}}$-level-$N$ modular function field. Let $W$ be the finite set of supersingular places (rational, affine-geometric, with $j$-value in the supersingular set), and let $R$ be a prolongation tuple over $P$ which is a model (the two divisor laws and the two cusp laws), satisfies the regularity law and node-value law for $W$ and the fixed-order law. Let $w\in W$ satisfy the value-integrality law, and fix a crossing presentation of $w$ over a number field $K\subset\overline{\mathbb{Q}}$: an element $\varpi$ of $A\cap K$ generating the kernel of $\mathrm{red}$ restricted to $A\cap K$, an $e_K\ge 1$ and a unit $\varepsilon$ with $q=\varpi^{e_K}\varepsilon$; node coordinates $c=(x,y)$ in the ring $R.\mathtt{nodeIntegersOver}\ K\ w$ (so $x$ has zero first residue and second residue of order $1$ at $\phi w$, and $y$ has zero second residue and first residue of order $1$ at $w$); a width $e_w\ge 1$ and a unit $u$ with $xy=\varpi^{e_we_K}u$ (constants embedded via $R.\mathtt{nodeConst}$); the ideal $(\varpi,x,y)$ maximal and the only maximal ideal; $(\varpi,x)$ and $(\varpi,y)$ prime with $y\notin(\varpi,x)$ and $x\notin(\varpi,y)$; the node ring Noetherian; and every element of it congruent to a constant modulo non-units. Let $f\neq 0$ lie in the level-$Nq$ function field over $\overline{\mathbb{Q}}$, with scalars $c_1,c_2$ such that $c_1f$ lies in $R_1$'s integers with nonzero residue and $c_2f$ lies in $R_2$'s integers with nonzero residue. Let $e$ be a finitely supported integer multiplicity function on places of the level-$Nq$ field, supported on places $V$ with $P.\mathtt{reduceFst}\,V=w$ which are strict on neither side, and assume $0\le V.\mathrm{ord}\,f+e(V)$ for every such $V$. Write $o_1=\mathrm{ord}_w$ of the first residue of $c_1f$, $o_2=\mathrm{ord}_{\phi w}$ of the second residue of $c_2f$ where $\phi$ is the arithmetic Frobenius semilinear automorphism, $M=\sum_{V}e(V)$ and $\Lambda=\prod_{V\in\operatorname{supp}e}v_A(V.\mathrm{evalAt}\,y)^{e(V)}$, all valuations being those of $A$. Then $v_A(q)^{e_w(o_1+M)}\le v_A(c_1c_2^{-1})\Lambda$ and $v_A(c_1c_2^{-1})\Lambda\, v_A(q)^{e_we_2}\le 1$ with $e_2=o_2$, and if either of these holds with equality then $V.\mathrm{ord}\,f+e(V)=0$ for every place $V$ over $w$ that is strict on neither side, and $o_1+M+o_2=0$.
--
--   This is the valuation-form chord estimate, together with its rigidity (equality) clause, attached to a single supersingular crossing of $X_0(Nq)$ in characteristic $q$: the two branches of the node are realised as annuli by the crossing presentation over a number field, and the orders of the two residues of $f$ on the two sheets are compared through the $v_A(q)$-scale of the node. It is the level-$N$ input to the annulus-datum form of the same bound, from which the comparison of divisors on the two components of the special fibre is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_pow_le_mul_prod_and_rigid_of_twist.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_pow_le_mul_prod_and_rigid_of_twist
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
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)

    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (hVI : R.ValueIntegralityLaw w)
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

    (f : ↥(modularFunctionFieldBar (N * q))) (hf0 : f ≠ 0)
    (c₁ c₂ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (hr₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (h₂ : c₂ • f ∈ R.R₂.integers) (hr₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)

    (e : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) →₀ ℤ)
    (he : ∀ V, e V ≠ 0 → P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
    (hpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → 0 ≤ V.ord f + e V) :

    A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
        ((ew : ℤ) * (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + ∑ V ∈ e.support, e V)) ≤
      A.valuation (c₁ * c₂⁻¹) *
        ∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) ^ e V ∧

    A.valuation (c₁ * c₂⁻¹) *
        (∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) ^ e V) *
        A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
          ((ew : ℤ) * (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) ≤ 1 ∧

    ((A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
          ((ew : ℤ) * (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + ∑ V ∈ e.support, e V)) =
        A.valuation (c₁ * c₂⁻¹) *
          ∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) ^ e V ∨
      A.valuation (c₁ * c₂⁻¹) *
          (∏ V ∈ e.support, A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q)))) ^ e V) *
          A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^
            ((ew : ℤ) * (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) = 1) →
      (∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          P.reduceFst V = w → ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → V.ord f + e V = 0) ∧
        w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (∑ V ∈ e.support, e V) +
          (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩) = 0) := by sorry
