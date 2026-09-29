-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mDivRepresents
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mDivRepresents
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/b5d1fd48-1d4a-56aa-839c-1ac12f86b708
-- title:
--   Incidence data representing m-division on the residue polydisc
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N\ge 1$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}:A\to k$, modular polynomial data $data$ of level $q$ satisfying the Kronecker congruence $hKr$, integrality hypotheses $h\alpha,h\beta$ for the two Hecke inclusions, and a place specialisation $P$ for these data; assume $q\nmid N$. Let $W$ be a finset of places of $modularFunctionFieldC\ k\ N$ whose members are exactly the supersingular places $ssPlaces\ q\ N\ k$, and let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws for strict places and the two cusp laws), the regularity law and node-value law for $W$, and the fixed-order law. Let $Q_1:\mathrm{Fin}\,d_1\to$ places of $modularFunctionFieldBar (N q)$ over $\overline{\mathbb Q}$ be strict of the first kind and $Q_2:\mathrm{Fin}\,d_2\to$ such places strict of the second kind, with $i\mapsto P.\mathrm{reduceFst}(Q_1 i)$ and $j\mapsto P.\mathrm{reduceSnd}(Q_2 j)$ injective, and let $T_1,T_2$ be the finsets of their reductions. Assume: $T_1$ is disjoint from $W$; every place in $T_1\cup T_2$ is affine-geometric, i.e. both $jGeomGen$ and $jNGeomGen$ lie in its valuation subring; every $v\in T_1\cup T_2$ admits a centre $c=(c_1,c_2)\in k\times k$ (both $jGeomGen-c_1$ and $jNGeomGen-c_2$ of positive order at $v$) which is the centre of no other place, and one of these two orders equals $1$; the values of $jGeomGen$ and $jNGeomGen$ at each reduced place are not fixed by the $q^2$-power map; general position, namely that any function regular off $T_1$ with order $\ge -1$ on $T_1$ and value $0$ at all $w\in W$ vanishes, and any function regular off $T_2$ with order $\ge -1$ on $T_2$ is constant; and $d_1+d_2=genusFF$ of $modularFunctionFieldBar (N q)$ over $\overline{\mathbb Q}$. Let further $Q_1',Q_2'$ be strict families of the same kinds with the same reductions as $Q_1,Q_2$, let $Q_s$ be strict of the first kind with reduction different from every $P.\mathrm{reduceFst}(Q_1 i)$, and let $m'\in\mathbb N$ with $m'+1$ invertible in $k$. Then there exist $h:\mathrm{Fin}((d_1+d_2)m'+1)\to modularFunctionFieldBar (N q)$, proofs that each $h_l$ lies in the integers of $R.R_1$ and of $R.R_2$, and incidence data $Dt$ of type $IncidenceSystem.Data\ (d_1+d_2)\ 2\ m'\ A$, such that $h_0=1$; each $h_l\ne 0$; for every $l$ and every place $V$, $\mathrm{ord}_V(h_l)\ge -\big(E'(V)+m'E_0(V)\big)$ where $E'=\sum_i Q_1'(i)+\sum_j Q_2'(j)$ and $E_0=\sum_i Q_1(i)+\sum_j Q_2(j)$ are the reduced divisors with coefficient $1$; for every $l$ the first residue $R.\mathrm{residue}_1 (h_l)$ has order $\ge 0$ off $T_1$ and $\ge -(m'+1)$ on $T_1$, the second residue $R.\mathrm{residue}_2 (h_l)$ has order $\ge 0$ off $T_2$ and $\ge -(m'+1)$ on $T_2$, and at each $w\in W$ there is $c\in k$ such that $R.\mathrm{residue}_1(h_l)$ has value $c$ at $w$ and $R.\mathrm{residue}_2(h_l)$ has value $c$ at $arithFrobC\ q\ k\ N\cdot w$; the family $l\mapsto (R.\mathrm{residue}_1(h_l),R.\mathrm{residue}_2(h_l))$ is linearly independent over $k$; and $P.MDivRepresents\ Q_1\ Q_2\ Q_1'\ Q_2'\ m'\ h\ Dt$ holds, the last condition asserting that at each of the $d_1+d_2$ base indices the data $Dt$ carries a generator triple of the level-$Nq$ field satisfying its two incidence equations, centred at the relevant reduction, through which the functions $h_l$ acquire local expressions with factor $(z-u_0)^{m'}(z-\tau)$ and denominators and Jacobians of non-zero reduction.
--
--   This is the chart-form existence statement underlying the divisibility argument on the residue polydisc of the Jacobian of $X_0(Nq)$: the Riemann–Roch family of functions integral for both Gauss prolongations is combined with local coordinates at the reductions of the base places into a single system of incidence data over $A$. It is used in the subsequent step computing orders of the two residues at prescribed places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mDivRepresents.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_IncidenceSystem
import Definitions.Def_MDivRepresents

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mDivRepresents
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
    (hT₁gen : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jGeomGen k N) ∧
      (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst (Q₁ i)).evalAt (jNGeomGen k N))
    (hT₂gen : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k N) ∧
      (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd (Q₂ j)).evalAt (jNGeomGen k N))
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
    (m' : ℕ) (hm : ((m' + 1 : ℕ) : k) ≠ 0) :
    ∃ (h : Fin ((d₁ + d₂) * m' + 1) → ↥(modularFunctionFieldBar (N * q)))
      (hh₁ : ∀ l, h l ∈ R.R₁.integers) (hh₂ : ∀ l, h l ∈ R.R₂.integers)
      (Dt : IncidenceSystem.Data (d₁ + d₂) 2 m' A),
      h 0 = 1 ∧
      (∀ l, h l ≠ 0) ∧
      (∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
        -(((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
          + (m' : ℤ) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)) ≤ V.ord (h l)) ∧
      (∀ l,
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₁, -((m' + 1 : ℕ) : ℤ) ≤ v.ord (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ v ∈ T₂, -((m' + 1 : ℕ) : ℤ) ≤ v.ord (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
        (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N)) c ∧
          (arithFrobC q k N • w).HasValue (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N)) c)) ∧
      LinearIndependent k (fun l =>
        ((R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N)))) ∧
      P.MDivRepresents Q₁ Q₂ Q₁' Q₂' m' h Dt := by sorry
