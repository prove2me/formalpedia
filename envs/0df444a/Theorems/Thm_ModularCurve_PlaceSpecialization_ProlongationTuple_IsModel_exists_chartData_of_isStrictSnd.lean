-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictSnd
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_chartData_of_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/cfb585ff-5de4-559c-ac35-15a786a2b900
-- title:
--   Chart data at a strict place of the second kind
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a level $N \neq 0$ with $q \nmid N$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$, and integrality of the two degeneracy inclusions from level $N$ to level $Nq$ over $\overline{\mathbb Q}$; let $P$ be a place specialisation with these data and write $F =$ `modularFunctionFieldBar (N * q)`. Let $W$ be a finite set of places of `modularFunctionFieldC k N` consisting exactly of the supersingular places `ssPlaces q N k`, and let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and node-value law for $W$, and the fixed-order law. Let $Q, Q'$ be places of $F$ over $\overline{\mathbb Q}$ that are strict of the second kind for $P$ (first reduction equal to the geometric Frobenius of the second reduction, the second reduction not fixed by the square of that Frobenius) with $P.\mathrm{reduceSnd}\,Q' = P.\mathrm{reduceSnd}\,Q =: \bar v$. Assume $\bar v$ is affine, i.e. both geometric generators `jGeomGen k N` and `jNGeomGen k N` lie in its valuation subring; that there is $c = (c_1,c_2) \in k^2$ which is a centre of $\bar v$ (both $\operatorname{ord}_{\bar v}(\tilde\jmath - c_1) > 0$ and $\operatorname{ord}_{\bar v}(\tilde\jmath_N - c_2) > 0$), such that $\bar v$ is the only place with centre $c$ and one of $\operatorname{ord}_{\bar v}(\tilde\jmath - c_1)$, $\operatorname{ord}_{\bar v}(\tilde\jmath_N - c_2)$ equals $1$; and that the residue values of $\tilde\jmath$ and of $\tilde\jmath_N$ at $\bar v$ both satisfy $x^{q^2} \neq x$. Finally fix $m' \in \mathbb N$ and $f_0,\dots,f_{n-1} \in F$ lying in the integers of the second regular prolongation $R.R_2$ and satisfying, for every place $V$ of $F$ that is strict of the second kind with second reduction $\bar v$, the bound $-\bigl(\delta_{V,Q'} + m'\,\delta_{V,Q}\bigr) \le \operatorname{ord}_V(f_l)$. Then there exist $z, y_1, y_2 \in F$, elements $u, \tau \in A$, jet coefficients $w_{j,r} \in A$ for $j \in \{0,1\}$ and $r \le m'$, polynomials $G_0, G_1$ and $p_l, s_l$ in $A[X_{\mathrm{none}}, X_0, X_1]$, and $\sigma_{l,r} \in A$, such that: $(z,y_1,y_2)$ is an admissible triple at $\bar v$ with constant $\mathrm{red}\,u$, meaning either $z = j(\mathfrak q^q)$, $y_1 = j(\mathfrak q^{Nq})$, $y_2 = j$ and $\operatorname{ord}_{\bar v}(\tilde\jmath - \mathrm{red}\,u) = 1$, or $z = j(\mathfrak q^{Nq})$, $y_1 = j(\mathfrak q^{q})$, $y_2 = j$ and $\operatorname{ord}_{\bar v}(\tilde\jmath_N - \mathrm{red}\,u) = 1$; both $G_j$ vanish on $(z, y_1, y_2)$ after mapping coefficients $A \to \overline{\mathbb Q} \to F$, and $G_0$ does not involve the variable $X_1$; $\operatorname{ord}_Q(z - u) > 0$, $\operatorname{ord}_Q(y_{j+1} - w_{j,0}) > 0$ for $j \in \{0,1\}$, $\operatorname{ord}_{Q'}(z - \tau) > 0$ and $\mathrm{red}\,\tau = \mathrm{red}\,u$; for each $l$ the value of $p_l$ at $(z,y_1,y_2)$ equals $f_l\,(z-u)^{m'}(z-\tau)$ times the value of $s_l$ at $(z,y_1,y_2)$; the reductions under $\mathrm{red}$ of $s_l(u, w_{0,0}, w_{1,0})$ and of $(\partial G_j/\partial X_j)(u, w_{0,0}, w_{1,0})$ are all nonzero; substituting $X_{\mathrm{none}} = u + T$ and $X_j = \sum_{r \le m'} w_{j,r}T^r$ into $G_j$ gives a polynomial in $T$ whose coefficients in degrees $0,\dots,m'$ all vanish; and the same substitution into $s_l$, multiplied by $\sum_{r \le m'} \sigma_{l,r}T^r$, gives $1$ in degrees $0,\dots,m'$.
--
--   This is the local, one-base-point half of the construction of the incidence data used to represent multiplication by $m$ on the residue polydisc attached to a base divisor, in the style of the inversion of multiplication by $m$ on a formal residue disc in Bosch–Lütkebohmert–Raynaud. It supplies coordinates $(z;y_1,y_2)$ on the modular function field of level $Nq$, an étale chain of two plane relations $G_0, G_1$ over $A$, local expressions $p_l/s_l$ for the given functions, and jets exact to order $m'$; the global assembly over all base points is carried out in [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mDivRepresents`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_mDivRepresents).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_chartData_of_isStrictSnd.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_chartData_of_isStrictSnd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictSnd Q) (hQ' : P.IsStrictSnd Q')
    (hQQ' : P.reduceSnd Q' = P.reduceSnd Q)
    (haff : IsAffineGeomPlace k N (P.reduceSnd Q))
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      (∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q) ∧
      ((P.reduceSnd Q).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.1) = 1 ∨
        (P.reduceSnd Q).ord (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c.2) = 1))
    (hgen : (P.reduceSnd Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jGeomGen k N) ∧
      (P.reduceSnd Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jNGeomGen k N))
    (m' : ℕ) {n : ℕ} (f : Fin n → ↥(modularFunctionFieldBar (N * q))) (hfI : ∀ l, f l ∈ R.R₂.integers)
    (hfd : ∀ l (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))), P.IsStrictSnd V → P.reduceSnd V = P.reduceSnd Q →
      -((Finsupp.single Q' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V
          + (m' : ℤ) * ((Finsupp.single Q (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V))
        ≤ V.ord (f l)) :
    ∃ (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u τ : A) (w : Fin 2 → Fin (m' + 1) → A)
      (G : Fin 2 → MvPolynomial (Option (Fin 2)) A) (p s : Fin n → MvPolynomial (Option (Fin 2)) A)
      (σ : Fin n → Fin (m' + 1) → A),
      PlaceSpecialization.IsSndTriple (q := q) (P.reduceSnd Q) (red u) z y₁ y₂ ∧
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
