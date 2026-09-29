-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/e713ced0-b145-5e9d-a713-a560a5c66619
-- title:
--   Strict two-sided representative of a good degree-zero class, level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality of the two degeneracy embeddings at level $1\cdot q$ ($h\alpha$, $h\beta$), a place specialisation $P$ for these data and a prolongation tuple $R$ for $P$. Assume $R$ satisfies `IsModel` (the two divisor laws and the two cusp laws), that the finset $W$ consists exactly of the supersingular places of $modularFunctionFieldC\ k\ 1$, and that $R$ satisfies the regularity law and node value law for $W$ and the fixed-place order law. Let $Q_1 : \mathrm{Fin}\,d_1$ and $Q_2 : \mathrm{Fin}\,d_2$ be families of places of $modularFunctionFieldBar (1\cdot q)$ over $\overline{\mathbb{Q}}$ with every $Q_1 i$ strict on the first side and every $Q_2 j$ strict on the second side (in the sense of `IsStrictFst`, `IsStrictSnd`: geometric Frobenius carries $reduceFst$ to $reduceSnd$, respectively $reduceSnd$ to $reduceFst$, and the square of Frobenius moves the relevant reduction), such that $i \mapsto P.reduceFst(Q_1 i)$ and $j \mapsto P.reduceSnd(Q_2 j)$ are injective; let $T_1$, $T_2$ be the finsets of their respective images, with $T_1$ disjoint from $W$ and all places of $T_1$ and $T_2$ affine geometric places (both $j$ and $j_N$ lie in the valuation ring). Assume two general-position hypotheses: every element $h$ of $modularFunctionFieldC\ k\ 1$ regular outside $T_1$, with at worst simple poles on $T_1$, and taking the value $0$ at every place of $W$, vanishes; and every $h$ regular outside $T_2$ with at worst simple poles on $T_2$ is a constant. Assume $d_1 + d_2$ equals $genusFF$ of $modularFunctionFieldBar (1\cdot q)$ over $\overline{\mathbb{Q}}$. Finally let $D$ be a degree-zero divisor each place of whose support is strict on the first or the second side, such that $P.glueData$ of $D$ for the node pairs $nodePairsOfPlaces (arithFrobC\ q\ k\ 1) W$ is admissible and its class in `GluedPic0` is zero. Then there exist families $Q_1'$, $Q_2'$ of the same sizes, again strict on the first, respectively second, side, with $P.reduceFst(Q_1' i) = P.reduceFst(Q_1 i)$ for all $i$ and $P.reduceSnd(Q_2' j) = P.reduceSnd(Q_2 j)$ for all $j$, such that the divisor $\bigl(\sum_i Q_1' i + \sum_j Q_2' j\bigr) - \bigl(\sum_i Q_1 i + \sum_j Q_2 j\bigr)$ has degree zero and its class in $\mathrm{Pic}^0$ equals the class of $D$.
--
--   This is a step in the analysis of the special fibre at $q$ of the modular curve of level $q$, whose two components are copies of the level-one curve glued along the supersingular places: a degree-zero class whose glued datum is trivial is represented by the difference of two effective divisors, each supported on places that are strict on one of the two sides and with prescribed reductions. It is used in the construction of degree-zero classes with prescribed inertia behaviour and in the proof that a good divisor with trivial glued class has trivial class in $\mathrm{Pic}^0$, the divisor-theoretic form of Mazur's principle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
    {d₁ d₂ : ℕ}
    (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k 1 v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k 1 v)
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k 1),
      (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k 1) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hgood : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))))
    (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
        (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W))
    (hmk : GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W)
        ⟨P.glueData (nodePairsOfPlaces (arithFrobC q k 1) W)
          (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))), hadm⟩ = 0) :
    ∃ (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      (∀ i, P.IsStrictFst (Q₁' i)) ∧ (∀ j, P.IsStrictSnd (Q₂' j)) ∧
      (∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j)) ∧
      ∃ hdeg0 : (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
          Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) ∈
            Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
        Pic0.mk ⟨_, hdeg0⟩ = Pic0.mk D := by sorry
