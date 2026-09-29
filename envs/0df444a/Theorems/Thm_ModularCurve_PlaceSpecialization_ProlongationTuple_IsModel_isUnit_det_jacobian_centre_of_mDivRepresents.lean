-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_isUnit_det_jacobian_centre_of_mDivRepresents
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.isUnit_det_jacobian_centre_of_mDivRepresents
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/835adcef-ae8e-5631-ad48-c79b8a4f0b2e
-- title:
--   Unit Jacobian at the centre of the m-division system
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N\ge 1$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red}\colon A\to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi \bmod q = (X'^q-X)(X'-X^q)$, integrality of the two degeneracy embeddings $\overline F_N\to\overline F_{Nq}$, and a place specialisation $P$ attached to these data; assume $q\nmid N$. Let $W$ be a finite set whose members are exactly the supersingular places of $F_{C,k,N}$ (rational, affine geometric, with $j$-value in `ssJSet q k`), and let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), `RegularityLaw W`, `NodeValueLaw W` and `OrderLawFixed`. Let $Q_1\colon \mathrm{Fin}\,d_1\to$ places of $\overline F_{Nq}$ be strict of the first kind and $Q_2\colon\mathrm{Fin}\,d_2\to$ places strict of the second kind, with $i\mapsto P.\mathrm{reduceFst}(Q_1 i)$ and $j\mapsto P.\mathrm{reduceSnd}(Q_2 j)$ injective and with images the finite sets $T_1$, $T_2$; assume $T_1$ disjoint from $W$, all places of $T_1\cup T_2$ affine geometric, each such place the unique place with its centre $c\in k\times k$ and with $\mathrm{ord}_v(j-c_1)=1$ or $\mathrm{ord}_v(j_N-c_2)=1$, the values of $j$ and $j_N$ at the reductions of the $Q_1 i$, $Q_2 j$ not fixed by $x\mapsto x^{q^2}$, and the two general-position conditions: a function regular off $T_1$ with at most simple poles on $T_1$ and value $0$ at every $w\in W$ vanishes, and a function regular off $T_2$ with at most simple poles on $T_2$ is constant. Assume $d_1+d_2$ equals the genus $\dim_{\overline{\mathbb Q}}H^1(0)$ of $\overline F_{Nq}$, and let $Q_1'$, $Q_2'$ be further strict families with the same reductions as $Q_1$, $Q_2$, and $Q_s$ a strict place of the first kind whose reduction differs from every $P.\mathrm{reduceFst}(Q_1 i)$. Let $m'\in\mathbb N$ and $h\colon\mathrm{Fin}((d_1+d_2)m'+1)\to\overline F_{Nq}$ with $h_0=1$, each $h_l$ in the integers of both $R.R_1$ and $R.R_2$, with $\mathrm{ord}_V(h_l)\ge -\bigl(E'(V)+m'E_0(V)\bigr)$ for all places $V$, where $E_0=\sum_i Q_1 i+\sum_j Q_2 j$ and $E'=\sum_i Q_1' i+\sum_j Q_2' j$; assume that the residues $R.\mathrm{residue}_1 h_l$, $R.\mathrm{residue}_2 h_l$ are regular off $T_1$, resp. $T_2$, have order $\ge -(m'+1)$ on $T_1$, resp. $T_2$, and that at each $w\in W$ the first residue has some value $c\in k$ at $w$ and the second has the same value at $\mathrm{arithFrob}_q\cdot w$, and that the pairs of residues are linearly independent over $k$. Finally let $Dt$ be incidence data of type [`IncidenceSystem.Data (d₁+d₂) 2 m' A`](def/IncidenceSystem.html#L18) with `P.MDivRepresents Q₁ Q₂ Q₁' Q₂' m' h Dt`, which requires for each index $i$ functions $z,y_1,y_2$ and an element $\tau\in A$ forming a first, resp. second, triple at the reduced place with centre $\mathrm{red}(u_{0,i})$, vanishing of the two equations $G_{i j}$ at $(z,y_1,y_2)$ with the last variable absent from $G_{i0}$, positivity of the orders of $z-u_{0,i}$, of $y_j-w_{0,i,j,0}$ and of $z-\tau$ at the corresponding places, the factorisations $p_{k,i}(z,y)=h_{k+1}\,(z-u_{0,i})^{m'}(z-\tau)\,s_{k,i}(z,y)$ together with the normalisations $p_{\mathrm{none},i}=(X-u_{0,i})^{m'}(X-\tau)$, $s_{\mathrm{none},i}=1$, $\sigma_{0,\mathrm{none},i}=\delta_0$, non-vanishing under $\mathrm{red}$ of the values $s$ and of the derivatives $dG$ at the centre, and a further clause constraining the centre at every variable of the system. If $(m'+1)\ne 0$ in $k$, then the determinant of the Jacobian matrix of the incidence system of $Dt$, evaluated at the centre of $Dt$, is a unit of $A$.
--
--   This is the invertibility-of-the-Jacobian input for the multivariate Hensel lemma applied to the incidence system encoding $(m'+1)$-division of divisor classes on $X_0(Nq)$ at a prime $q\nmid N$, the centre being the reduction-theoretic approximate solution supplied by the glued special fibre. It is used in the construction of a place of $\overline F_{Nq}$ with prescribed first and second reductions and prescribed order, the statement [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_reduceFst_eq_reduceSnd_eq_ord_eq_nsmul_sub_sub_of_evalAt_pow_ne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_reduceFst_eq_reduceSnd_eq_ord_eq_nsmul_sub_sub_of_evalAt_pow_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_isUnit_det_jacobian_centre_of_mDivRepresents.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.isUnit_det_jacobian_centre_of_mDivRepresents
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
    (m' : ℕ) (h : Fin ((d₁ + d₂) * m' + 1) → ↥(modularFunctionFieldBar (N * q))) (hh0 : h 0 = 1)
    (hh₁ : ∀ l, h l ∈ R.R₁.integers)
    (hhL : ∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      -(((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
        + (m' : ℤ) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)) ≤ V.ord (h l))
    (hh₂ : ∀ l, h l ∈ R.R₂.integers)
    (hhland : ∀ l,
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₁ → 0 ≤ v.ord (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ v ∈ T₁, -((m' + 1 : ℕ) : ℤ) ≤ v.ord (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ v : Place k ↥(modularFunctionFieldC k N), v ∉ T₂ → 0 ≤ v.ord (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ v ∈ T₂, -((m' + 1 : ℕ) : ℤ) ≤ v.ord (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N))) ∧
      (∀ w ∈ W, ∃ c : k, w.HasValue (R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N)) c ∧
        (arithFrobC q k N • w).HasValue (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N)) c))
    (hhind : LinearIndependent k (fun l =>
      ((R.residue₁ ⟨h l, hh₁ l⟩ : ↥(modularFunctionFieldC k N)), (R.residue₂ ⟨h l, hh₂ l⟩ : ↥(modularFunctionFieldC k N)))))
    (Dt : IncidenceSystem.Data (d₁ + d₂) 2 m' A) (hrep : P.MDivRepresents Q₁ Q₂ Q₁' Q₂' m' h Dt)
    (hm : ((m' + 1 : ℕ) : k) ≠ 0) :
    IsUnit (Dt.jacobian Dt.centre).det := by sorry
