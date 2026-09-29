-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/33919c24-b2bd-5f42-8761-c799f2052fc8
-- title:
--   Rigidity of a two-sided base divisor under a torsion relation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi \equiv (X'^{\,q}-X)(X'-X^{q}) \pmod q$, integrality hypotheses $h\alpha, h\beta$ for the two degeneracy maps from level $1$ to level $1\cdot q$, a place specialisation $P$ and a prolongation tuple $R$ for it satisfying `IsModel` (the two divisor laws and the two cusp laws), together with a finset $W$ consisting exactly of the supersingular places of the level-one geometric function field over $k$, the node value law and the regularity law for $W$. Given $d_1, d_2 \in \mathbb N$ and families $Q_1, Q_1' : \mathrm{Fin}\,d_1$ and $Q_2, Q_2' : \mathrm{Fin}\,d_2$ of places of $\overline{\mathbb Q}$-rational function field at level $1\cdot q$, with the $Q_1$'s and $Q_1'$'s strict of the first kind (Frobenius carries the first reduction to the second, and the square of Frobenius moves the first reduction) and the $Q_2$'s and $Q_2'$'s strict of the second kind, such that $i \mapsto P.\mathrm{reduceFst}(Q_1 i)$ and $j \mapsto P.\mathrm{reduceSnd}(Q_2 j)$ are injective and $P.\mathrm{reduceFst}(Q_1' i) = P.\mathrm{reduceFst}(Q_1 i)$, $P.\mathrm{reduceSnd}(Q_2' j) = P.\mathrm{reduceSnd}(Q_2 j)$; let $T_1$, $T_2$ be the finsets of the places $P.\mathrm{reduceFst}(Q_1 i)$, resp. $P.\mathrm{reduceSnd}(Q_2 j)$, with $T_1$ disjoint from $W$, all places of $T_1 \cup T_2$ affine geometric (both $j$ and $j_N$ are regular there), and the $j$-value at each place of $T_1$ and of $T_2$ different from $0$ and $1728$. Assume the general-position conditions: every function $h$ on the level-one curve over $k$ that is regular off $T_1$, has at worst simple poles on $T_1$ and vanishes at every $w \in W$ is zero; and every $h$ regular off $T_2$ with at worst simple poles on $T_2$ is a constant. Assume further a place $Q_s$ strict of the first kind whose first reduction differs from every $P.\mathrm{reduceFst}(Q_1 i)$, a natural number $n$ nonzero in $k$, and a nonzero $f$ at level $1 \cdot q$ whose order at every place $V$ equals $n$ times the coefficient at $V$ of $\bigl(\sum_i Q_1' i + \sum_j Q_2' j\bigr) - \bigl(\sum_i Q_1 i + \sum_j Q_2 j\bigr)$. Then the two effective divisors agree: $\sum_i Q_1' i + \sum_j Q_2' j = \sum_i Q_1 i + \sum_j Q_2 j$.
--
--   This is the rigidity step in the Mazur-style analysis of torsion relations on the Jacobian of $X_0(q)$: a divisor supported on two Frobenius-related families of points, in general position and avoiding the supersingular nodes and the points with $j = 0, 1728$, cannot be moved by an $n$-torsion linear equivalence. It is the level-one case, and it feeds the construction of degree-zero divisor classes with prescribed inertia behaviour and the vanishing criterion for the class of a good divisor in $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hNV : R.NodeValueLaw W) (hRL : R.RegularityLaw W)
    {d₁ d₂ : ℕ}
    (Q₁ Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i))
    (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k 1 v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k 1 v)
    (hQ₁j : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ≠ 0 ∧ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ≠ 1728)
    (hQ₂j : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ≠ 0 ∧ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ≠ 1728)
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k 1) c)
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (n : ℕ) (hn : (n : k) ≠ 0) (f : ↥(modularFunctionFieldBar (1 * q))) (hf : f ≠ 0)
    (hdiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      V.ord f = (n : ℤ) * (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
        - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V)) :
    (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) =
      ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by sorry
