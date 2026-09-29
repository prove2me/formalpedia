-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_of_saturated
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_crossingPresentation_nodeIntegersOver_of_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/81b9a2ba-3f33-52e5-8020-e0cec91f0248
-- title:
--   Crossing presentation at an arbitrary supersingular node
-- statement:
--   Fix a prime $q$ with $5 \le q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \neq 0$ with $q \nmid N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two Hecke maps $\bar\alpha, \bar\beta$ in level $N\cdot q$ over $\overline{\mathbb{Q}}$, a place specialization $P$ for these data and a prolongation tuple $R$ of $P$. Let $K \subset \overline{\mathbb{Q}}$ be a finite extension of $\mathbb{Q}$, and let $w$ be a place of the level-$N$ function field $\mathrm{modularFunctionFieldC}\,k\,N$ lying in $\mathrm{ssPlaces}\,q\,N\,k$, i.e. $w$ is rational, is an affine geometric place, and its value on the geometric $j$-generator lies in the supersingular $j$-set; assume $w$ is fixed by the square of the coefficient-Frobenius semilinear automorphism $\varphi = \mathrm{arithFrobC}\,q\,k\,N$. Two compatibility hypotheses are imposed: for every place $V$ of $\mathrm{modularFunctionFieldBar}\,(N q)$ with $P.\mathrm{reduceFst}\,V = w$, every $g$ in the node ring $R.\mathrm{nodeIntegers}\,w$ (the elements integral for $R_1$, for $R_2$, and for all such $V$) and every value $c$ of $g$ at $V$, one has $c \in A$ and $\mathrm{red}\,c$ is the value of $R.\mathrm{nodeResidue}_1\,w\,g$ at $w$ (hypothesis `hsp₁`), respectively the value of $R.\mathrm{nodeResidue}_2\,w\,g$ at $\varphi \cdot w$ (hypothesis `hsp₂`). Two saturation hypotheses are imposed on $B := R.\mathrm{nodeIntegersOver}\,K\,w$, the subring of elements of the node ring whose Laurent expansion lies in the field $\mathrm{fieldOver}\,(Nq)\,K$: if $g, g' \in B$ and the first residue of $g$ has positive order at $w$ while that of $g'$ has order exactly $1$, then the first residue of $g$ is the product of the first residue of $g'$ with the first residue of some $b \in B$, and symmetrically for the second residues and the place $\varphi \cdot w$. Let $c_0$ be a datum of node coordinates over $K$ at $w$, that is a pair $(x_0, y_0)$ in $B$ with first residue of $x_0$ zero and second residue of order $1$ at $\varphi\cdot w$, and second residue of $y_0$ zero and first residue of order $1$ at $w$. Finally let $\varpi \in \mathrm{coeffSubring}\,A\,K = A \cap K$ be such that an element $d$ of $A \cap K$ has $\mathrm{redRestrict}\,\mathrm{red}\,K\,d = 0$ precisely when $\varpi$ divides $d$ in $A \cap K$. Then there is a datum $c = (x,y)$ of node coordinates over $K$ at $w$ with $(\tilde\varpi, x) = (\tilde\varpi, x_0)$ and $(\tilde\varpi, y) = (\tilde\varpi, y_0)$ as ideals of $B$, where $\tilde\varpi = R.\mathrm{nodeConst}\,K\,w\,\varpi$ is the image of $\varpi$ under the constants homomorphism $A \cap K \to B$; there are $e_K \ge 1$ and a unit $\varepsilon$ of $A \cap K$ with $q = \varpi^{e_K}\varepsilon$; and there are $E \ge 1$ and a unit $u$ of $B$ with $x y = \tilde\varpi^{\,E} u$, such that the ideal $(\tilde\varpi, x, y)$ is maximal and is the only maximal ideal of $B$, the ideals $(\tilde\varpi, x)$ and $(\tilde\varpi, y)$ are prime, $y \notin (\tilde\varpi, x)$ and $x \notin (\tilde\varpi, y)$.
--
--   This is the local crossing (ordinary double point) presentation of the level-$Nq$ modular curve over $A \cap K$ at a supersingular node, in the places-based vocabulary of the node ring $B$: two branches $(\tilde\varpi, x)$, $(\tilde\varpi, y)$ meeting in the unique closed point, with $xy$ a unit times $\tilde\varpi^{E}$. It is the form of the crossing statement with the restrictions $j(w) \neq 0$ and $j(w) \neq 1728$ removed, and feeds the variant `exists_crossingPresentation_nodeIntegersOver_of_orderLawFixed_of_saturated_of_five_le`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_crossingPresentation_nodeIntegersOver_of_saturated.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open ModularCurve
open ModularCurve.PlaceSpecialization
open ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_crossingPresentation_nodeIntegersOver_of_saturated
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w)
    (hsp₁ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
      V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
      ∃ hcA : c ∈ A,
      w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩))
    (hsp₂ : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
      ∀ (g : ↥(R.nodeIntegers w)) (c : AlgebraicClosure ℚ),
      V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) c →
      ∃ hcA : c ∈ A,
      (arithFrobC q k N • w).HasValue (R.nodeResidue₂ w g : ↥(modularFunctionFieldC k N)) (red ⟨c, hcA⟩))
    (hsat₁ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩)
    (hsat₂ : ∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩)
    (c₀ : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d') :
    ∃ c : R.NodeCoordinates K w,
      Ideal.span {R.nodeConst K w ϖ, c.x} = Ideal.span {R.nodeConst K w ϖ, c₀.x} ∧
      Ideal.span {R.nodeConst K w ϖ, c.y} = Ideal.span {R.nodeConst K w ϖ, c₀.y} ∧
    ∃ (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)), 1 ≤ eK ∧ IsUnit ε ∧
      ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε ∧
    ∃ (E : ℕ) (u : ↥(R.nodeIntegersOver K w)), 1 ≤ E ∧ IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ E * u ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x, c.y}).IsMaximal ∧
      (∀ M : Ideal ↥(R.nodeIntegersOver K w), M.IsMaximal → M = Ideal.span {R.nodeConst K w ϖ, c.x, c.y}) ∧
      (Ideal.span {R.nodeConst K w ϖ, c.x}).IsPrime ∧ (Ideal.span {R.nodeConst K w ϖ, c.y}).IsPrime ∧
      c.y ∉ Ideal.span {R.nodeConst K w ϖ, c.x} ∧ c.x ∉ Ideal.span {R.nodeConst K w ϖ, c.y} := by sorry
