-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sectionPair_bounds_of_regularityLaw_of_isModel_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.sectionPair_bounds_of_regularityLaw_of_isModel_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/69ca1a60-e13a-5627-a226-955175e24a84
-- title:
--   Section-pair bounds from the regularity law, level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with modular polynomial data `data` for $q$ satisfying the Kronecker congruence `hKr`, integrality hypotheses `hα`, `hβ` for the two Hecke degeneracy embeddings at auxiliary level $1$ and prime $q$, a place specialisation $P$ and a prolongation tuple $R$ for $P$. Assume `hR : R.IsModel`, i.e. the two divisor laws and the two cusp laws hold, that the finset $W$ consists exactly of the supersingular places of `modularFunctionFieldC k 1`, and that $R$ satisfies the regularity law for $W$. Let $Q_1 : \mathrm{Fin}\,d_1$ and $Q_2 : \mathrm{Fin}\,d_2$ be families of places of `modularFunctionFieldBar (1 * q)` with every $Q_1(i)$ strictly first-side and every $Q_2(j)$ strictly second-side for $P$, with $i \mapsto P.\mathrm{reduceFst}(Q_1 i)$ and $j \mapsto P.\mathrm{reduceSnd}(Q_2 j)$ injective, and let $T_1$, $T_2$ be the finsets of their images under `P.reduceFst`, `P.reduceSnd` respectively; assume $T_1$ disjoint from $W$ and all places in $T_1 \cup T_2$ affine geometric (both $j$ and $j_N$ lie in the valuation subring). Let $E \ge 0$ and $D$ be divisors on `modularFunctionFieldBar (1 * q)`, $D$ good for $P$ (each place of its support strictly first- or strictly second-side), and let $G$ lie in the integers of both regular prolongations $R_1$, $R_2$, with $E - (\sum_i Q_1 i + \sum_j Q_2 j) - D$ equal to the divisor of $G$. Let $hb_1, hb_2$ be non-zero elements of `modularFunctionFieldC k 1` whose divisors are the pushforwards along `P.reduceFst`, `P.reduceSnd` of the strictly-first and strictly-second parts `P.fstDiv D`, `P.sndDiv D` of $D$, and assume that for each $w \in W$ there is a non-zero $c \in k$ with $hb_1$ having value $c$ at $w$ and $hb_2$ having value $c$ at $\mathrm{arithFrobC}\,q\,k\,1 \cdot w$. The conclusion is a conjunction of five assertions about the products $g_1 = R.\mathrm{residue}_1\langle G\rangle \cdot hb_1$ and $g_2 = R.\mathrm{residue}_2\langle G\rangle \cdot hb_2$: $\mathrm{ord}_v(g_1) \ge 0$ for $v \notin T_1$ and $\mathrm{ord}_v(g_1) \ge -1$ for $v \in T_1$; likewise $\mathrm{ord}_v(g_2) \ge 0$ for $v \notin T_2$ and $\ge -1$ for $v \in T_2$; and for every $w \in W$ there is a $c \in k$ (not required non-zero) such that $g_1$ has value $c$ at $w$ and $g_2$ has value $c$ at $\mathrm{arithFrobC}\,q\,k\,1 \cdot w$.
--
--   This is the level-one instance ($N = 1$, so the level is the prime $q$ itself) of the statement that the pair of reductions of a bi-integral function, corrected by the two auxiliary functions $hb_1$, $hb_2$ cutting out the reduced base divisor, is a section of the glued two-component special fibre with at worst simple poles along the reduced strict points and matching values at the supersingular gluing points. It feeds the existence theorem [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne), which produces strict points with prescribed reductions and prescribed class in $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sectionPair_bounds_of_regularityLaw_of_isModel_levelOne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.sectionPair_bounds_of_regularityLaw_of_isModel_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k 1))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (hRL : R.RegularityLaw W)
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
    (E D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE : 0 ≤ E)
    (hD : P.IsGoodDiv D)
    (G : ↥(modularFunctionFieldBar (1 * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
    (hdiv : ∀ V, (E - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) - D) V
      = V.ord G)
    (hb₁ hb₂ : ↥(modularFunctionFieldC k 1)) (hb₁0 : hb₁ ≠ 0) (hb₂0 : hb₂ ≠ 0)
    (hdiv₁ : ∀ v, Finsupp.mapDomain P.reduceFst (P.fstDiv D) v = v.ord hb₁)
    (hdiv₂ : ∀ v, Finsupp.mapDomain P.reduceSnd (P.sndDiv D) v = v.ord hb₂)
    (hvals : ∀ w ∈ W, ∃ c : k, c ≠ 0 ∧ w.HasValue hb₁ c ∧ (arithFrobC q k 1 • w).HasValue hb₂ c) :
    (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨G, h₁⟩ * hb₁)) ∧
    (∀ v ∈ T₁, -1 ≤ v.ord (R.residue₁ ⟨G, h₁⟩ * hb₁)) ∧
    (∀ v : Place k ↥(modularFunctionFieldC k 1), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨G, h₂⟩ * hb₂)) ∧
    (∀ v ∈ T₂, -1 ≤ v.ord (R.residue₂ ⟨G, h₂⟩ * hb₂)) ∧
    (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨G, h₁⟩ * hb₁) c ∧
      (arithFrobC q k 1 • w).HasValue (R.residue₂ ⟨G, h₂⟩ * hb₂) c) := by sorry
