-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/f17c7b3c-a070-598f-9a0d-c7685d70088b
-- title:
--   Rigidity of a two-sided base divisor under n-torsion relations
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N\neq 0$ with $q\nmid N$, an algebraically closed field $k$ of characteristic $q$ with a ring homomorphism $red:A\to k$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two Hecke degeneracy embeddings $\overline{\mathcal F}_N\to\overline{\mathcal F}_{Nq}$, and a place specialisation $P$ of these data. Let $R$ be a prolongation tuple for $P$ which is a model (the two divisor laws and the two cusp laws comparing $\mathrm{ord}_V f$ upstairs with the orders of the two residues $R.\mathrm{residue}_1 f$, $R.\mathrm{residue}_2 f$ downstairs), let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k`, and assume $R$ satisfies the node-value law and the regularity law for $W$. Let $Q_1,Q_1':\mathrm{Fin}\,d_1$ be families of places of `modularFunctionFieldBar (N*q)` over $\overline{\mathbb Q}$ all satisfying $P.\mathrm{IsStrictFst}$ (the geometric Frobenius at level $N$ carries $\mathrm{reduceFst}$ to $\mathrm{reduceSnd}$, and its square moves $\mathrm{reduceFst}$), and $Q_2,Q_2':\mathrm{Fin}\,d_2$ families satisfying $P.\mathrm{IsStrictSnd}$ (the dual condition on $\mathrm{reduceSnd}$). Assume $i\mapsto P.\mathrm{reduceFst}(Q_1\,i)$ and $j\mapsto P.\mathrm{reduceSnd}(Q_2\,j)$ are injective, that $P.\mathrm{reduceFst}(Q_1'\,i)=P.\mathrm{reduceFst}(Q_1\,i)$ and $P.\mathrm{reduceSnd}(Q_2'\,j)=P.\mathrm{reduceSnd}(Q_2\,j)$, and let $T_1,T_2$ be the finite sets of places consisting of the $P.\mathrm{reduceFst}(Q_1\,i)$, respectively the $P.\mathrm{reduceSnd}(Q_2\,j)$. Assume $T_1$ is disjoint from $W$, every place of $T_1$ and of $T_2$ is an affine geometric place (both $j$ and $j_N$ lie in its valuation ring), and for each $i$ and each $j$ the value of $j$ at $P.\mathrm{reduceFst}(Q_1\,i)$, respectively at $P.\mathrm{reduceSnd}(Q_2\,j)$, is neither $0$ nor $1728$. Assume the general-position conditions: any $h$ in `modularFunctionFieldC k N` regular outside $T_1$, with $\mathrm{ord}_v h\ge -1$ for $v\in T_1$, and with value $0$ at every $w\in W$, vanishes; and any $h$ regular outside $T_2$ with $\mathrm{ord}_v h\ge-1$ for $v\in T_2$ is a constant. Let $Q_*$ be a further place satisfying $P.\mathrm{IsStrictFst}$ whose $\mathrm{reduceFst}$ differs from every $P.\mathrm{reduceFst}(Q_1\,i)$, let $n$ be a natural number invertible in $k$, and let $f\neq0$ in `modularFunctionFieldBar (N*q)` satisfy $\mathrm{ord}_V f=n\bigl(\sum_i Q_1'\,i+\sum_j Q_2'\,j-\sum_i Q_1\,i-\sum_j Q_2\,j\bigr)(V)$ for all places $V$. Then the divisors coincide: $\sum_i Q_1'\,i+\sum_j Q_2'\,j=\sum_i Q_1\,i+\sum_j Q_2\,j$.
--
--   This is the level-$N$, two-sided rigidity statement for base divisors on $X_0(Nq)_{\overline{\mathbb Q}}$ made of strict points of the two kinds, in the coordinate form where the local parameter $j-j(Q)$ is available, whence the exclusion of the values $j=0,1728$. It feeds the arguments on torsion classes in the degree-zero divisor class group of the glued special fibre, in particular the statements that a good class killed by $n$ vanishes and that good classes with trivial image are divisible by $n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hNV : R.NodeValueLaw W) (hRL : R.RegularityLaw W)
    {d₁ d₂ : ℕ}
    (Q₁ Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂ Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁ : ∀ i, P.IsStrictFst (Q₁ i)) (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i))
    (hQ₂ : ∀ j, P.IsStrictSnd (Q₂ j)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hinj₁ : Function.Injective fun i => P.reduceFst (Q₁ i))
    (hinj₂ : Function.Injective fun j => P.reduceSnd (Q₂ j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    {T₁ T₂ : Finset (Place k ↥(modularFunctionFieldC k N))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁ i) = v)
    (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂ j) = v)
    (hT₁W : Disjoint T₁ W)
    (hT₁aff : ∀ v ∈ T₁, IsAffineGeomPlace k N v) (hT₂aff : ∀ v ∈ T₂, IsAffineGeomPlace k N v)
    (hQ₁j : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ≠ 0 ∧ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ≠ 1728)
    (hQ₂j : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ≠ 0 ∧ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ≠ 1728)
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (n : ℕ) (hn : (n : k) ≠ 0) (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ≠ 0)
    (hdiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V.ord f = (n : ℤ) * (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
        - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)) :
    (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) =
      ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by sorry
