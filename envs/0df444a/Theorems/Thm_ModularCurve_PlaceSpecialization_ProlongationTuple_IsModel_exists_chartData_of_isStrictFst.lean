-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictFst
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_chartData_of_isStrictFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/0e8c9563-bf34-5c45-a418-1fd496405770
-- title:
--   Chart data at a strict first-kind place over a fixed reduction
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, $N\ge 1$ with $q\nmid N$, an algebraically closed field $k$ of characteristic $q$, a ring map $\mathrm{red}\colon A\to k$, modular polynomial data for $q$ satisfying the Kronecker congruence, integrality of the two Hecke maps from level $N$ to level $Nq$, and a place specialisation $P$; let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\ k\ N$ consisting exactly of the supersingular places, and let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), `RegularityLaw W`, `NodeValueLaw W` and `OrderLawFixed`. Let $Q,Q'$ be places of $F=\mathrm{modularFunctionFieldBar}(N q)$ over $\overline{\mathbb Q}$, both strict of the first kind (Frobenius carries the first reduction to the second, and the square of Frobenius moves the first reduction), with $\bar v:=P.\mathrm{reduceFst}\,Q'=P.\mathrm{reduceFst}\,Q$. Assume $\bar v$ is affine geometric (both $jGeomGen$ and $jNGeomGen$ lie in its valuation subring); that some $c=(c_1,c_2)\in k\times k$ is a centre of $\bar v$, is the centre of no other place, and satisfies $\mathrm{ord}_{\bar v}(jGeomGen-c_1)=1$ or $\mathrm{ord}_{\bar v}(jNGeomGen-c_2)=1$; and that the residue values $\bar v(jGeomGen)$, $\bar v(jNGeomGen)$ are both moved by $x\mapsto x^{q^2}$. Let $m'\in\mathbb N$ and $f_0,\dots,f_{n-1}\in F$ lie in $R.R_1.\mathrm{integers}$ and satisfy $-\bigl([V=Q']+m'[V=Q]\bigr)\le \mathrm{ord}_V(f_l)$ for every place $V$ strict of the first kind with $P.\mathrm{reduceFst}\,V=\bar v$. Then there are $z,y_1,y_2\in F$, elements $u,\tau\in A$, coefficients $w_{j,r}\in A$ for $j<2$, $r\le m'$, polynomials $G_0,G_1$ and $p_l,s_l$ in $A[X_{o}]$ with variables indexed by $\mathrm{Option}(\mathrm{Fin}\,2)$, and $\sigma_{l,r}\in A$, such that: $(z,y_1,y_2)$ with the value $\mathrm{red}\,u$ is an `IsFstTriple` at $\bar v$, i.e. $(z,y_1,y_2)$ is $(j,j_N,j_{Nq})$ with $\mathrm{ord}_{\bar v}(jGeomGen-\mathrm{red}\,u)=1$ or $(j_N,j,j_{Nq})$ with $\mathrm{ord}_{\bar v}(jNGeomGen-\mathrm{red}\,u)=1$; both $G_j$ vanish on $(z,y_1,y_2)$ after mapping coefficients $A\to\overline{\mathbb Q}\to F$, and $G_0$ does not involve the variable indexed by $1$; $\mathrm{ord}_Q(z-u)>0$, $\mathrm{ord}_Q(y_{j+1}-w_{j,0})>0$ for $j<2$, $\mathrm{ord}_{Q'}(z-\tau)>0$ and $\mathrm{red}\,\tau=\mathrm{red}\,u$; for each $l$, $p_l(z,y_1,y_2)=f_l\,(z-u)^{m'}(z-\tau)\,s_l(z,y_1,y_2)$; the reductions under $\mathrm{red}$ of $s_l$ and of $\partial G_j/\partial Y_j$ at the point $(u,w_{0,0},w_{1,0})$ are all nonzero; and the truncated jet identities hold, namely for $j<2$ and $r\le m'$ the $T^r$-coefficient of $G_j$ evaluated at $X=u+T$, $Y_{j'}=\sum_{r'\le m'}w_{j',r'}T^{r'}$ vanishes, and for each $l$ and $r\le m'$ the $T^r$-coefficient of $\bigl(\sum_{r'\le m'}\sigma_{l,r'}T^{r'}\bigr)\,s_l(u+T,\dots)-1$ vanishes.
--
--   This is the local, one-base-point construction of chart data on a residue polydisc: local coordinates oriented by a uniformiser at the reduced place, a pair of plane equations that is étale in the relevant derivatives, local factorisations of the given functions along the divisor $Q'+m'Q$, and jets of the branch and of the inverse of $s_l$ exact to order $m'$, all with coefficients in $A$. It is used in the assembly of incidence data representing multiplication by $m$ over all base points, in [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mDivRepresents`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mDivRepresents).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictFst.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_MDivRepresents

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_chartData_of_isStrictFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictFst Q) (hQ' : P.IsStrictFst Q')
    (hQQ' : P.reduceFst Q' = P.reduceFst Q)
    (haff : IsAffineGeomPlace k N (P.reduceFst Q))
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceFst Q) ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceFst Q) ∧
      ((P.reduceFst Q).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        (P.reduceFst Q).ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hgen : (P.reduceFst Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst Q).evalAt (jGeomGen k N) ∧
      (P.reduceFst Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst Q).evalAt (jNGeomGen k N))
    (m' : ℕ) {n : ℕ} (f : Fin n → ↥(modularFunctionFieldBar (N * q))) (hfI : ∀ l, f l ∈ R.R₁.integers)
    (hfd : ∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.IsStrictFst V → P.reduceFst V = P.reduceFst Q →
      -((Finsupp.single Q' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V
          + (m' : ℤ) * ((Finsupp.single Q (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V))
        ≤ V.ord (f l)) :
    ∃ (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u τ : A) (w : Fin 2 → Fin (m' + 1) → A)
      (G : Fin 2 → MvPolynomial (Option (Fin 2)) A) (p s : Fin n → MvPolynomial (Option (Fin 2)) A)
      (σ : Fin n → Fin (m' + 1) → A),
      PlaceSpecialization.IsFstTriple (q := q) (P.reduceFst Q) (red u) z y₁ y₂ ∧
      (∀ j : Fin 2, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (G j) = 0) ∧
      (some 1 : Option (Fin 2)) ∉ (G 0).vars ∧
      0 < Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)) ∧
      (∀ j : Fin 2, 0 < Q.ord (![y₁, y₂] j - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w j 0 : AlgebraicClosure ℚ))) ∧
      0 < Q'.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) ∧
      red τ = red u ∧
      (∀ l, PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (p l) =
        f l * (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)) ^ m' *
          (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (τ : AlgebraicClosure ℚ)) *
          PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) (s l)) ∧
      (∀ l, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0)) (s l)) ≠ 0) ∧
      (∀ j : Fin 2, red (MvPolynomial.eval (fun o : Option (Fin 2) => Option.elim o u (fun j => w j 0))
        (MvPolynomial.pderiv (some j) (G j))) ≠ 0) ∧
      (∀ (j : Fin 2) (r : Fin (m' + 1)),
        (MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (G j)).coeff r = 0) ∧
      (∀ (l : Fin n) (r : Fin (m' + 1)),
        ((∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (σ l r')) *
            MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m' + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (s l) - 1).coeff r = 0) := by sorry
