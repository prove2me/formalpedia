-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_linearIndependent_residue_pair_riemannRochSpace_add_nsmul
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_linearIndependent_residue_pair_riemannRochSpace_add_nsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/c07d1c92-11e1-50e9-ac3a-6120cddb7a15
-- title:
--   Bi-integral family in L(E'+(m-1)E₀) with independent residue pairs
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N\neq 0$ with $q\nmid N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red\colon A\to k$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two Hecke maps $\bar\alpha,\bar\beta$ at level $(N,q)$, and a place specialisation $P$ of these data. Let $W$ be a finite set of places of $modularFunctionFieldC\ k\ N$ whose members are exactly the supersingular places for $q,N,k$, and let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and node-value law for $W$, and `OrderLawFixed`. Let $Q_1\colon\mathrm{Fin}\ d_1\to$ places of $modularFunctionFieldBar (N q)$ be strictly first-type for $P$ and $Q_2\colon\mathrm{Fin}\ d_2\to$ places strictly second-type, with $i\mapsto P.reduceFst(Q_1 i)$ and $j\mapsto P.reduceSnd(Q_2 j)$ injective; let $T_1$, $T_2$ be the finite sets of these first, respectively second, reductions, with $T_1$ disjoint from $W$. All places of $T_1\cup T_2$ are assumed affine geometric (both $jGeomGen$ and $jNGeomGen$ lie in the valuation ring), and each $v$ in $T_1$ or $T_2$ is assumed to have a centre $c=(c_1,c_2)\in k\times k$, in the sense that $v$ has positive order at $jGeomGen-c_1$ and at $jNGeomGen-c_2$, which is the centre of no other place, and with one of these two orders equal to $1$. Two general-position hypotheses are imposed: a function with no poles outside $T_1$, poles at most simple on $T_1$, and value $0$ at every $w\in W$ vanishes; a function with no poles outside $T_2$ and poles at most simple on $T_2$ is a constant. Assume $d_1+d_2=genusFF\ \overline{\mathbb Q}\ (modularFunctionFieldBar (N q))$. Let $Q_1'$, $Q_2'$ be further families of strictly first- and second-type places with $P.reduceFst(Q_1' i)=P.reduceFst(Q_1 i)$ and $P.reduceSnd(Q_2' j)=P.reduceSnd(Q_2 j)$, let $Q_s$ be a strictly first-type place whose first reduction differs from every $P.reduceFst(Q_1 i)$, and let $m$ be a natural number with $m\neq 0$ in $k$. Writing $E_0=\sum_i Q_1 i+\sum_j Q_2 j$ and $E'=\sum_i Q_1' i+\sum_j Q_2' j$, the conclusion asserts the existence of $m(d_1+d_2)-(d_1+d_2)+1$ elements $h_l$ of $modularFunctionFieldBar (N q)$, all lying in the integers of both $R.R_1$ and $R.R_2$, with $h_0=1$, each $h_l\neq 0$, each $h_l$ in the Riemann–Roch space of $E'+(m-1)E_0$ (that is, $-\bigl(E'(V)+(m-1)E_0(V)\bigr)\le \mathrm{ord}_V(h_l)$ for every place $V$), and such that for each $l$ the residues $\bar h_l^{(1)}=R.residue_1(h_l)$ and $\bar h_l^{(2)}=R.residue_2(h_l)$ have nonnegative order outside $T_1$ respectively $T_2$, order at least $-m$ on $T_1$ respectively $T_2$, and for every $w\in W$ there is $c\in k$ with $\bar h_l^{(1)}$ taking the value $c$ at $w$ and $\bar h_l^{(2)}$ taking the value $c$ at the translate of $w$ by the arithmetic Frobenius semilinear automorphism $arithFrobC\ q\ k\ N$; finally, the pairs $(\bar h_l^{(1)},\bar h_l^{(2)})$ are linearly independent over $k$.
--
--   This is the linear-algebra input for the reduction of linear systems on the two-component special fibre of $X_0(Nq)$ at $q$: a family spanning the Riemann–Roch space of $E'+(m-1)E_0$ by elements integral for both prolongations, whose pairs of residues are sections on the glued fibre with poles bounded by $mT_1$, $mT_2$ and matching values at the node pairs $(w,\mathrm{Frob}\cdot w)$, $w\in W$, and are independent over $k$. It is used in the construction of $m$-divisor representatives (`exists_mDivRepresents`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_linearIndependent_residue_pair_riemannRochSpace_add_nsmul.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_linearIndependent_residue_pair_riemannRochSpace_add_nsmul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
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
    (hT₁sm : ∀ v ∈ T₁, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hT₂sm : ∀ v ∈ T₂, ∃ c : k × k, IsCentreOf k N c v ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = v) ∧
      (v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        v.ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hgp₁ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) →
      (∀ w ∈ W, w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : ↥(modularFunctionFieldC k N),
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) →
      ∃ c : k, h = algebraMap k ↥(modularFunctionFieldC k N) c)
    (hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hQ₁' : ∀ i, P.IsStrictFst (Q₁' i)) (hQ₂' : ∀ j, P.IsStrictSnd (Q₂' j))
    (hred₁ : ∀ i, P.reduceFst (Q₁' i) = P.reduceFst (Q₁ i))
    (hred₂ : ∀ j, P.reduceSnd (Q₂' j) = P.reduceSnd (Q₂ j))
    (Qs : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQs : P.IsStrictFst Qs)
    (hQs' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁ i))
    (m : ℕ) (hm : (m : k) ≠ 0) :
    ∃ (h : Fin (m * (d₁ + d₂) - (d₁ + d₂) + 1) → ↥(modularFunctionFieldBar (N * q)))
      (h₁ : ∀ l, h l ∈ R.R₁.integers) (h₂ : ∀ l, h l ∈ R.R₂.integers),
      h 0 = 1 ∧
      (∀ l, h l ≠ 0) ∧
      (∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        -(((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            + ((m : ℤ) - 1) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)) ≤ V.ord (h l)) ∧
      (∀ l,
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₁, -(m : ℤ) ≤ v.ord (R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₂, -(m : ℤ) ≤ v.ord (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N)) c ∧
          (arithFrobC q k N • w).HasValue (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N)) c)) ∧
      LinearIndependent k (fun l =>
        ((R.residue₁ ⟨h l, h₁ l⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨h l, h₂ l⟩ : ↥(modularFunctionFieldC k N)))) := by sorry
