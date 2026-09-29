-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/1e8f154a-a76a-5a8d-acbd-6643f1b5002c
-- title:
--   Inertia-stable node telescoping identity at a supersingular crossing
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N$, an algebraically closed perfect field $k$ of characteristic $q$, a ring map $red : A \to k$, modular polynomial data satisfying the Kronecker congruence, integrality of the two Hecke embeddings, a place specialisation $P$ and a prolongation tuple $R$ over $P$; assume $q \nmid N$, that $R$ satisfies `IsModel` (the two divisor laws and the two cusp laws) and `OrderLawFixed`, and fix a finite set $W_0$ of supersingular places of `modularFunctionFieldC k N` on which the regularity law and the node value law hold. Fix intermediate fields $K \le K'$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $K'$ finite over $\mathbb{Q}$, a place $w \in W_0$ with $\varphi w :=$ `arithFrobC q k N` $\cdot\, w \in W_0$, the value integrality law at $w$, and the inclusion $R.\mathrm{nodeIntegersOver}\,K\,w \subseteq R.\mathrm{nodeIntegersOver}\,K'\,w$. Further data: an element $\varpi$ of $\mathrm{coeffSubring}\,A\,K'$ whose multiples are exactly the elements killed by `redRestrict red K'`, an exponent $e_K \ge 1$ and a unit $\varepsilon$ with $q = \varpi^{e_K}\varepsilon$; node coordinates $c = (x,y)$ over $K$ at $w$, an exponent $e_w \ge 1$ and a unit $u$ of the node ring over $K'$ with $xy = (\mathrm{nodeConst}\,K'\,w\,\varpi)^{e_w e_K}u$; the hypotheses that $(\varpi, x, y)$ generates a maximal ideal which is the only maximal ideal and equals the maximal ideal of the (local, Noetherian) node ring, that $(\varpi,x)$ and $(\varpi,y)$ are prime with $y$ outside the first and $x$ outside the second, and that no element of the node ring is a unit after subtracting a suitable constant; a depth function $\mathrm{depthQ}$ with, for every place $V$ of `modularFunctionFieldBar (N * q)` lying over $w$ via $P.\mathrm{reduceFst}$ and strict on neither side, $\mathrm{depthQ}(V) > 0$ and $A$-valuation of $V(y)$ raised to the denominator of $\mathrm{depthQ}(V)$ equal to the $A$-valuation of $q$ raised to its numerator. Finally, let $f \ne 0$ lie in $\mathrm{fieldOver}(N q)\,K'$, assume that field is the fraction field of the node ring over $K'$, let $c_1, c_2 \in K'^{\times}$ be scalings with $c_i \cdot f$ integral for $R_1$, resp. $R_2$, with nonzero residue, let $D$ be the divisor $V \mapsto V.\mathrm{ord}\,f$, assume $D$ is invariant under the inertia subgroup of $A$ over $\mathbb{Q}$ on the part of its support lying over $w$, let $m \in \mathbb{Z}$ be the depth moment $\sum_V D(V)\,\mathrm{depthQ}(V)$ over the places of the support over $w$ strict on neither side, assume the corresponding end count $\sum_V D(V)$ equals $\mathrm{ord}_w(R.\mathrm{residue}_1(c_1 f)) + \mathrm{ord}_{\varphi w}(R.\mathrm{residue}_2(c_2 f))$, write $c_i = \varpi^{m_i}\eta_i$ with $\eta_i$ units, and let $\bar\eta_1, \bar\eta_2, \bar\varepsilon \in k^\times$ be the reductions of $\eta_1, \eta_2, \varepsilon$, $u_0 \in k^\times$ the value at $w$ of the first node residue of $u$, and $\Theta \in k^\times$ the reduction under $red$ of $\bigl(\prod_V V(y)^{-D(V)}\bigr) q^{m}$ (assumed to lie in $A$), the product again over the places of the support over $w$ strict on neither side. Then there are units $\alpha_1, \alpha_2$ of $k$ such that $R.\mathrm{residue}_1(c_1 f)$ divided by the $\mathrm{ord}_w$-th power of the first node residue of $y$ has value $\alpha_1$ at $w$, $R.\mathrm{residue}_2(c_2 f)$ divided by the $\mathrm{ord}_{\varphi w}$-th power of the second node residue of $x$ has value $\alpha_2$ at $\varphi w$, and $$\frac{\alpha_1}{\alpha_2} = \frac{\bar\eta_1}{\bar\eta_2}\,(-1)^{\sum_V D(V)}\,u_0^{\;\mathrm{ord}_{\varphi w}(R.\mathrm{residue}_2(c_2 f))}\,\bar\varepsilon^{-m}\,\Theta.$$
--
--   This is the orbit form of the node telescoping identity at a supersingular crossing of the reduction of the modular curve of level $Nq$: the two normalised branch reductions of a single function $f$, scaled along the two branches, have values at $w$ and at its Frobenius translate whose ratio is given explicitly by the coefficient units, a sign from the end count, the crossing unit, the ramification unit of $q$ and one angular residue $\Theta$ built from the values of the node coordinate $y$ on the places over $w$; only inertia-stability of the part of the support over $w$ is required, not pointwise fixedness. It is used in the annulus-datum comparisons, at level $N$ and over $\mathbb{Q}$, which deduce end-order inequalities and coupled scalings for twists with vanishing class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecialization
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_hasValue_residueFst_div_pow_and_residueSnd_div_pow_and_div_eq_angFactor_of_inertiaStable
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W₀ : Finset (Place k (modularFunctionFieldC k N))) (hW₀ : ∀ v ∈ W₀, v ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W₀) (hval : R.NodeValueLaw W₀)

    (K K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKK' : K ≤ K') [FiniteDimensional ℚ K']
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W₀) (hwφ : arithFrobC q k N • w ∈ W₀) (hVI : R.ValueIntegralityLaw w)
    (hBB' : R.nodeIntegersOver K w ≤ R.nodeIntegersOver K' w)

    (ϖ : ↥(NodeLocalized.coeffSubring A K'))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K'), NodeLocalized.redRestrict red K' d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (heK : 1 ≤ eK) (ε : ↥(NodeLocalized.coeffSubring A K')) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K')) = ϖ ^ eK * ε)

    (c : R.NodeCoordinates K w) (ew : ℕ) (hew : 1 ≤ ew)
    (u : ↥(R.nodeIntegersOver K' w)) (hu : IsUnit u)
    (hxy : (c.x : ↥(modularFunctionFieldBar (N * q))) * c.y = (R.nodeConst K' w ϖ : ↥(modularFunctionFieldBar (N * q))) ^ (ew * eK) * u)
    (hmax : (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y}).IsMaximal ∧
        ∀ M : Ideal ↥(R.nodeIntegersOver K' w), M.IsMaximal → M = Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y})
    [IsLocalRing ↥(R.nodeIntegersOver K' w)] [IsNoetherianRing ↥(R.nodeIntegersOver K' w)]
    (hmax' : maximalIdeal ↥(R.nodeIntegersOver K' w) = Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x, Subring.inclusion hBB' c.y})
    (hbr : (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.y}).IsPrime ∧
        Subring.inclusion hBB' c.y ∉ Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.x} ∧ Subring.inclusion hBB' c.x ∉ Ideal.span {R.nodeConst K' w ϖ, Subring.inclusion hBB' c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K' w), ∃ o : ↥(NodeLocalized.coeffSubring A K'), ¬ IsUnit (g - R.nodeConst K' w o))

    (depthQ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℚ)
    (hdepthQ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
        0 < depthQ V ∧ c.yDepth V ^ (depthQ V).den = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ (depthQ V).num.toNat)

    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ≠ 0)
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (N * q) K')
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K', ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K' w ∧ y ∈ R.nodeIntegersOver K' w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    (c₁ c₂ : AlgebraicClosure ℚ) (h₁ : c₁ • f ∈ R.R₁.integers) (hu₁ : R.R₁.residue ⟨c₁ • f, h₁⟩ ≠ 0)
    (h₂ : c₂ • f ∈ R.R₂.integers) (hu₂ : R.R₂.residue ⟨c₂ • f, h₂⟩ ≠ 0)
    (hc₁ : c₁ ∈ K') (hc₂ : c₂ ∈ K') (hc₁0 : c₁ ≠ 0) (hc₂0 : c₂ ≠ 0)

    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hDf : ∀ V, D V = V.ord f)

    (hstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ V ∈ D.support, P.reduceFst V = w →
      D (arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V) = D V)

    (m : ℤ) (hm : (∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (D V : ℚ) * depthQ V) = m)
    (hN : (∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V) =
      w.ord (R.residue₁ ⟨c₁ • f, h₁⟩) + (arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩))
    (m₁ m₂ : ℤ) (η₁ η₂ : ↥(NodeLocalized.coeffSubring A K')) (hη₁ : IsUnit η₁) (hη₂ : IsUnit η₂)
    (hc₁η : c₁ = ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ m₁ *
      ((η₁ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ))
    (hc₂η : c₂ = ((ϖ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ) ^ m₂ *
      ((η₂ : ↥(NodeLocalized.coeffSubring A K')) : AlgebraicClosure ℚ))
    (ηbar₁ ηbar₂ εbar u0 : kˣ)
    (hηbar₁ : NodeLocalized.redRestrict red K' η₁ = (ηbar₁ : k))
    (hηbar₂ : NodeLocalized.redRestrict red K' η₂ = (ηbar₂ : k))
    (hεbar : NodeLocalized.redRestrict red K' ε = (εbar : k))
    (hu0 : w.HasValue ((R.nodeResidue₁ w ⟨(u : ↥(modularFunctionFieldBar (N * q))), u.2.1⟩ :
      ↥(modularFunctionFieldC k N)) : ↥(modularFunctionFieldC k N)) (u0 : k))
    (Θ : kˣ)
    (hΘ : ∃ hmem : (∏ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), V.evalAt ((c.y : ↥(modularFunctionFieldBar (N * q)))) ^ (-(D V))) *
        ((q : ℕ) : AlgebraicClosure ℚ) ^ m ∈ A, red ⟨_, hmem⟩ = (Θ : k)) :
    ∃ α₁ α₂ : kˣ,
      w.HasValue
        ((R.residue₁ ⟨c₁ • f, h₁⟩ : ↥(modularFunctionFieldC k N)) /
          (R.nodeResidue₁ w ⟨(c.y : ↥(modularFunctionFieldBar (N * q))), c.y.2.1⟩ : ↥(modularFunctionFieldC k N)) ^
            (w.ord (R.residue₁ ⟨c₁ • f, h₁⟩)))
        (α₁ : k) ∧
      (arithFrobC q k N • w).HasValue
        ((R.residue₂ ⟨c₂ • f, h₂⟩ : ↥(modularFunctionFieldC k N)) /
          (R.nodeResidue₂ w ⟨(c.x : ↥(modularFunctionFieldBar (N * q))), c.x.2.1⟩ : ↥(modularFunctionFieldC k N)) ^
            ((arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)))
        (α₂ : k) ∧
      α₁ / α₂ =
        (ηbar₁ / ηbar₂) *
        (-1 : kˣ) ^ (∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V) *
        u0 ^ ((arithFrobC q k N • w).ord (R.residue₂ ⟨c₂ • f, h₂⟩)) *
        εbar ^ (-m) * Θ := by sorry
