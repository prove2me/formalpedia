-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sectionPair_bounds_of_regularityLaw_of_isModel
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.sectionPair_bounds_of_regularityLaw_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/ba39a2c3-b45d-5e3b-8b83-1719bdfec6de
-- title:
--   Divisor bounds for the reduced pair of a bi-integral section
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$ with $q \nmid N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, data $\Phi$ for the modular polynomial of level $q$ satisfying the Kronecker congruence $\Phi \bmod q = (\Phi_{C X}^{q} - X)(C X - X^{q})$ in the stated form, integrality of the two degeneracy embeddings $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$ over $\overline{\mathbb Q}$, and a place specialisation $P$ from places of $\mathrm{modularFunctionFieldBar}\,N$ to places of $\mathrm{modularFunctionFieldC}\,k\,N$. Let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), let $W$ be a finset whose members are exactly the supersingular places of the level-$N$ fibre (rational, affine geometric, with $j$-value in the supersingular set), and assume $R$ satisfies `RegularityLaw W`. Let $Q_1 : \mathrm{Fin}\,d_1 \to$ places of level $Nq$ be strict of the first kind ($\varphi(\mathrm{reduceFst}\,Q_{1,i}) = \mathrm{reduceSnd}\,Q_{1,i}$ and $\varphi^2(\mathrm{reduceFst}\,Q_{1,i}) \neq \mathrm{reduceFst}\,Q_{1,i}$, where $\varphi = \mathrm{frobOnPlacesGeomLevel}$), and $Q_2 : \mathrm{Fin}\,d_2 \to$ places strict of the second kind, with $i \mapsto \mathrm{reduceFst}(Q_{1,i})$ and $j \mapsto \mathrm{reduceSnd}(Q_{2,j})$ injective; let $T_1$, $T_2$ be the finsets of their respective images, with $T_1$ disjoint from $W$ and all places of $T_1 \cup T_2$ affine geometric (both $j$ and $j_N$ in the valuation ring). Let $E \geq 0$ and $D$ be divisors of level $Nq$ with every place in the support of $D$ strict of the first or second kind, and let $G$ lie in the integers of both $R.R_1$ and $R.R_2$ with $\mathrm{div}\,G = E - \sum_i Q_{1,i} - \sum_j Q_{2,j} - D$ pointwise. Finally let $\bar h_1, \bar h_2$ be nonzero elements of $\mathrm{modularFunctionFieldC}\,k\,N$ whose divisors are the push-forwards along $\mathrm{reduceFst}$, resp. $\mathrm{reduceSnd}$, of the strict-first, resp. strict-second, part of $D$, and assume that for every $w \in W$ there is $c \neq 0$ in $k$ with $\bar h_1$ having value $c$ at $w$ and $\bar h_2$ having value $c$ at $\mathrm{arithFrobC}\,q\,k\,N \cdot w$. Then, writing $u_1 = R.\mathrm{residue}_1(G)\,\bar h_1$ and $u_2 = R.\mathrm{residue}_2(G)\,\bar h_2$: $\mathrm{ord}_v u_1 \geq 0$ for every place $v \notin T_1$ and $\mathrm{ord}_v u_1 \geq -1$ for $v \in T_1$; likewise $\mathrm{ord}_v u_2 \geq 0$ for $v \notin T_2$ and $\geq -1$ for $v \in T_2$; and for every $w \in W$ there is $c \in k$ such that $u_1$ has value $c$ at $w$ and $u_2$ has value $c$ at $\mathrm{arithFrobC}\,q\,k\,N \cdot w$.
--
--   This is the level-$N$, two-sided form of the statement that the pair of residues of a section integral for both prolongations is a section of the glued special fibre of $X_0(Nq)$, with poles confined to the reduced base points $T_1$, $T_2$ and matching values across the supersingular nodes. Its conclusion is precisely the input needed for the $h^0 = 1$ argument on the glued fibre, and it is used in the two existence results producing strict places of the first and second kind with prescribed reductions and equal classes in $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sectionPair_bounds_of_regularityLaw_of_isModel.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.sectionPair_bounds_of_regularityLaw_of_isModel
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (E D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hE : 0 ≤ E)
    (hD : P.IsGoodDiv D)
    (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
    (hdiv : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V
      = V.ord G)
    (hb₁ hb₂ : ↥(modularFunctionFieldC k N)) (hb₁0 : hb₁ ≠ 0) (hb₂0 : hb₂ ≠ 0)
    (hdiv₁ : ∀ v, Finsupp.mapDomain P.reduceFst (P.fstDiv D) v = v.ord hb₁)
    (hdiv₂ : ∀ v, Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v = v.ord hb₂)
    (hvals : ∀ w ∈ W, ∃ c : k, c ≠ 0 ∧ w.HasValue hb₁ c ∧ (arithFrobC q k N • w).HasValue hb₂ c) :
    (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨G, h₁⟩ * hb₁)) ∧
    (∀ v ∈ T₁, -1 ≤ v.ord (R.residue₁ ⟨G, h₁⟩ * hb₁)) ∧
    (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨G, h₂⟩ * hb₂)) ∧
    (∀ v ∈ T₂, -1 ≤ v.ord (R.residue₂ ⟨G, h₂⟩ * hb₂)) ∧
    (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨G, h₁⟩ * hb₁) c ∧
      (arithFrobC q k N • w).HasValue (R.residue₂ ⟨G, h₂⟩ * hb₂) c) := by sorry
