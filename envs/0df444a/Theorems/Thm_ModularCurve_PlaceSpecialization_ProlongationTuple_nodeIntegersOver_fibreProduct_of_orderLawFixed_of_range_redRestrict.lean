-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeIntegersOver_fibreProduct_of_orderLawFixed_of_range_redRestrict
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.nodeIntegersOver_fibreProduct_of_orderLawFixed_of_range_redRestrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/de3a03d4-4095-5a05-b602-6c6a99ae998b
-- title:
--   Fibre-product and saturation laws for the K-node ring
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \neq 0$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two Hecke maps $\bar\alpha, \bar\beta$ from level $N$ to level $Nq$, a place specialisation $P$ for these data, and a prolongation tuple $R$ for $P$. Assume $q \nmid N$, that $R$ satisfies `IsModel` (the two divisor laws and the cusp laws at $\infty$ and at $0$) and `OrderLawFixed`, and that for a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\ k\ N$, all supersingular in the sense of `ssPlaces q N k`, the laws `RegularityLaw W` and `NodeValueLaw W` hold. Let $K \subseteq \overline{\mathbb{Q}}$ be a number field such that every $a \in k$ with $a^{q^2} = a$ lies in the image of the reduction $A \cap K \to k$ induced by $red$; let $w \in W$, let $c$ be a datum of node coordinates $x, y$ over $K$ at $w$ (so $x, y$ lie in the node ring $S = R.\mathrm{nodeIntegersOver}\ K\ w$ with $\mathrm{res}_1 x = 0$, $\mathrm{ord}_{\varphi \cdot w}(\mathrm{res}_2 x) = 1$, $\mathrm{res}_2 y = 0$, $\mathrm{ord}_w(\mathrm{res}_1 y) = 1$, where $\varphi = \mathrm{arithFrobC}\ q\ k\ N$), and let $\varpi \in A \cap K$ generate the kernel of that reduction, in the sense that $d \in A \cap K$ reduces to $0$ precisely when $d$ is a multiple of $\varpi$. Then, writing $\mathrm{res}_1, \mathrm{res}_2$ for the two node residue maps on $S$ and $\varpi$ also for its image as a constant in $S$: (i) for $g \in S$ one has $\mathrm{res}_1 g = 0$ and $\mathrm{res}_2 g = 0$ simultaneously if and only if $g \in \varpi S$; (ii) if $\mathrm{res}_1 g = 0$ then $g - xb \in \varpi S$ for some $b \in S$; (iii) if $\mathrm{res}_2 g = 0$ then $g - yb \in \varpi S$ for some $b \in S$; (iv) if $\mathrm{ord}_w(\mathrm{res}_1 g) > 0$ and $\mathrm{ord}_w(\mathrm{res}_1 g') = 1$ then $\mathrm{res}_1 g = \mathrm{res}_1 g' \cdot \mathrm{res}_1 b$ for some $b \in S$; (v) the same statement for $\mathrm{res}_2$ with orders taken at $\varphi \cdot w$; and (vi) for every $g \in S$ both $\mathrm{ord}_w(\mathrm{res}_1 g) \geq 0$ and $\mathrm{ord}_{\varphi \cdot w}(\mathrm{res}_2 g) \geq 0$.
--
--   This is the local algebra of the special fibre of $X_0(Nq)$ at $q$ near a supersingular point, in the form needed to recognise the node ring over a number field $K$: items (i)–(iii) express $S/\varpi S$ as the fibre product of $S/(\varpi, x)$ and $S/(\varpi, y)$ over $S/(\varpi, x, y)$, while (iv)–(vi) say that each residue map has image saturated in the local ring of its component and takes non-negative orders. It is the source of the separate statements describing the kernels of the individual residue maps, such as [`ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidueFst_eq_zero_iff_mem_span_of_orderLawFixed_of_range_redRestrict`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidueFst_eq_zero_iff_mem_span_of_orderLawFixed_of_range_redRestrict).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeIntegersOver_fibreProduct_of_orderLawFixed_of_range_redRestrict.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem
ModularCurve.PlaceSpecialization.ProlongationTuple.nodeIntegersOver_fibreProduct_of_orderLawFixed_of_range_redRestrict
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K))
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    (∀ g : ↥(R.nodeIntegersOver K w),
      (R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∧ R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0) ↔ g ∈ Ideal.span {R.nodeConst K w ϖ}) ∧
    (∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 →
      ∃ b : ↥(R.nodeIntegersOver K w), g - c.x * b ∈ Ideal.span {R.nodeConst K w ϖ}) ∧
    (∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 →
      ∃ b : ↥(R.nodeIntegersOver K w), g - c.y * b ∈ Ideal.span {R.nodeConst K w ϖ}) ∧
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩) ∧
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩) ∧
    (∀ g : ↥(R.nodeIntegersOver K w),
      0 ≤ w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) ∧ 0 ≤ (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩)) := by sorry
