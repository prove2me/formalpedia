-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_reduceFst_eq_reduceSnd_eq_ord_eq_of_mDivRepresents_of_forall_eval_eq_zero
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_reduceFst_eq_reduceSnd_eq_ord_eq_of_mDivRepresents_of_forall_eval_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/9dc64d79-f704-51c7-b572-09b6e6c19232
-- title:
--   Roots of the incidence system give m-division divisors
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an integer $N\ge 1$ with $q\nmid N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red:A\to k$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two degeneracy embeddings $\bar\alpha,\bar\beta$ from level $N$ to level $Nq$, and a place specialisation $P$ for these data. Let $W$ be a finset consisting exactly of the supersingular places of the level-$N$ geometric function field over $k$, and let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), `RegularityLaw W`, `NodeValueLaw W` and `OrderLawFixed`. Let $Q_1:\mathrm{Fin}\,d_1\to$ places of the level-$Nq$ function field over $\overline{\mathbb Q}$ be strict of the first kind and $Q_2:\mathrm{Fin}\,d_2\to$ such places strict of the second kind, with $i\mapsto P.\mathrm{reduceFst}(Q_1 i)$ and $j\mapsto P.\mathrm{reduceSnd}(Q_2 j)$ injective, and let $T_1,T_2$ be the finsets of their reductions, $T_1$ disjoint from $W$. Assume: every place of $T_1\cup T_2$ is an affine geometric place (both $j$- and $j_N$-generators lie in its valuation ring); every $v\in T_1\cup T_2$ has a centre $c\in k\times k$ (both $\mathrm{ord}_v(j-c_1)$ and $\mathrm{ord}_v(j_N-c_2)$ positive) which is the centre of no other place, with at least one of these two orders equal to $1$; at each $P.\mathrm{reduceFst}(Q_1 i)$ and each $P.\mathrm{reduceSnd}(Q_2 j)$ the values of the $j$- and $j_N$-generators are not fixed by $x\mapsto x^{q^2}$; any function on the level-$N$ field over $k$ regular off $T_1$, with at most simple poles on $T_1$ and value $0$ at every $w\in W$, vanishes, and any function regular off $T_2$ with at most simple poles on $T_2$ is constant; and $d_1+d_2$ equals the genus of the level-$Nq$ function field over $\overline{\mathbb Q}$. Let further $Q_1',Q_2'$ be families, strict of the first and second kind, with the same reductions as $Q_1,Q_2$; let $Q_s$ be strict of the first kind with reduction distinct from all $P.\mathrm{reduceFst}(Q_1 i)$; let $m'\in\mathbb N$ and $h:\mathrm{Fin}((d_1+d_2)m'+1)\to$ level-$Nq$ field with $h_0=1$, every $h_l$ in the valuation subring of the first regular prolongation $R.R_1$, and $\mathrm{ord}_V(h_l)\ge -(E'(V)+m'E_0(V))$ for every place $V$, where $E_0=\sum_i Q_1 i+\sum_j Q_2 j$ and $E'=\sum_i Q_1' i+\sum_j Q_2' j$ as divisors. Finally let $Dt$ be incidence data of type $(d_1+d_2,2,m')$ over $A$ with $P.\mathrm{MDivRepresents}\,Q_1\,Q_2\,Q_1'\,Q_2'\,m'\,h\,Dt$ (the compatibility tying $Dt$ to the modular situation: for each index a local triple $z,y_1,y_2$ and a constant $\tau\in A$ realising a first- or second-kind triple at the relevant reduction, vanishing of the branch polynomials $G_{ij}$, the prescribed factorisations of the $p$- and $s$-polynomials in terms of the $h_l$, and non-vanishing after $red$ of the relevant denominators and derivatives), and let $Pt$ assign to each incidence variable an element of $A$ congruent to $Dt.\mathrm{centre}$ modulo the maximal ideal of $A$ and annihilating every equation of the system, $\mathrm{eval}_{Pt}(Dt.\mathrm{system}\,v)=0$ for all $v$. Then there exist families $Q_1''$ and $Q_2''$, strict of the first and second kind respectively, with $P.\mathrm{reduceFst}(Q_1'' i)=P.\mathrm{reduceFst}(Q_1 i)$ and $P.\mathrm{reduceSnd}(Q_2'' j)=P.\mathrm{reduceSnd}(Q_2 j)$, and a nonzero $f$ in the level-$Nq$ function field such that for every place $V$, $\mathrm{ord}_V f=(m'+1)E''(V)-E'(V)-m'E_0(V)$, where $E''=\sum_i Q_1'' i+\sum_j Q_2'' j$.
--
--   This is the half of the polydisc divisibility argument for $J_0(Nq)$ at $q\nmid N$ which converts a solution of the incidence system of $m$-division, $m=m'+1$, into an actual linear equivalence $mE''\sim E'+m'E_0$ on the level-$Nq$ curve, the points of $E''$ reducing to the same places as those of $E_0$ and keeping their strict first/second kind. It is used by [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_reduceFst_eq_reduceSnd_eq_ord_eq_nsmul_sub_sub_of_evalAt_pow_ne`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_reduceFst_eq_reduceSnd_eq_ord_eq_nsmul_sub_sub_of_evalAt_pow_ne), the form in which divisibility on the residue polydisc enters the specialisation of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_reduceFst_eq_reduceSnd_eq_ord_eq_of_mDivRepresents_of_forall_eval_eq_zero.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_reduceFst_eq_reduceSnd_eq_ord_eq_of_mDivRepresents_of_forall_eval_eq_zero
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
    (Dt : IncidenceSystem.Data (d₁ + d₂) 2 m' A) (hrep : P.MDivRepresents Q₁ Q₂ Q₁' Q₂' m' h Dt)
    (Pt : IncidenceSystem.Var (d₁ + d₂) 2 m' → A)
    (hPt : ∀ v, Pt v - Dt.centre v ∈ IsLocalRing.maximalIdeal A)
    (hroot : ∀ v, MvPolynomial.eval Pt (Dt.system v) = 0) :
    ∃ (Q₁'' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (Q₂'' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))),
      (∀ i, P.IsStrictFst (Q₁'' i)) ∧ (∀ j, P.IsStrictSnd (Q₂'' j)) ∧
      (∀ i, P.reduceFst (Q₁'' i) = P.reduceFst (Q₁ i)) ∧
      (∀ j, P.reduceSnd (Q₂'' j) = P.reduceSnd (Q₂ j)) ∧
      ∃ f : ↥(modularFunctionFieldBar (N * q)), f ≠ 0 ∧
        ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          V.ord f =
            ((m' + 1 : ℕ) : ℤ) * ((∑ i, Finsupp.single (Q₁'' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂'' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            - ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V)
            - (m' : ℤ) * ((∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) :
                Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V) := by sorry
