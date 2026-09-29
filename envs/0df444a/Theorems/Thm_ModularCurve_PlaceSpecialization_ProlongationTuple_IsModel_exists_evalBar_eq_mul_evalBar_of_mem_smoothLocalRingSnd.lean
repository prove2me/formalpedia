-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/650df8bf-6a37-5598-a8fb-31786cf4fb5a
-- title:
--   Regular functions on a strict second-kind disc as p/s
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; let `data` be a modular polynomial datum for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the pair $(j, j(q\tau))$ of $q$-expansions), `hKr` the congruence that its reduction mod $q$ equals $(Y^{q}-X)(Y-X^{q})$, and `hα`, `hβ` the integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$N$ into the level-$Nq$ base-changed modular function field. Let $P$ be a place specialisation for these data, assume $q \nmid N$, let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k`, and let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node-value law for $W$, and `OrderLawFixed`. Let $Q$ be a place of `modularFunctionFieldBar (N * q)` that is strict of the second kind for $P$, i.e. $P.\mathrm{reduceFst}\,Q$ is the geometric Frobenius image of $\bar v := P.\mathrm{reduceSnd}\,Q$ while the square of that Frobenius does not fix $\bar v$. Assume both generators `jGeomGen k N` and `jNGeomGen k N` lie in the valuation subring of $\bar v$; that some $c \in k \times k$ is a centre of $\bar v$ (both generators minus the corresponding coordinate of $c$ have positive order at $\bar v$) and is the centre of no other place; and that the values of the two generators at $\bar v$ are not fixed by raising to the $q^{2}$-th power. Let $z, y_1, y_2$ lie in the level-$Nq$ field, $u \in A$, $w : \mathrm{Fin}\,2 \to A$, and suppose $(\bar v, \mathrm{red}\,u, z, y_1, y_2)$ satisfies `IsSndTriple`: either $z = j(q\tau)$, $y_1 = j(Nq\tau)$, $y_2 = j$ with $\mathrm{ord}_{\bar v}(\mathrm{jGeomGen} - \mathrm{red}\,u) = 1$, or $z = j(Nq\tau)$, $y_1 = j(q\tau)$, $y_2 = j$ with the same condition for `jNGeomGen`. Suppose further that $z - u$ and each $y_j - w_j$ have positive order at $Q$. Then for every $f$ in `R.smoothLocalRingSnd` $\bar v$, that is, every $f$ lying in the valuation subring $R.R_2.\mathrm{integers}$ and in the valuation subring of every place of the level-$Nq$ field which is strict of the second kind with second reduction $\bar v$, there exist polynomials $p, s \in A[X_{\mathrm{none}}, X_0, X_1]$ with $p(z, y_1, y_2) = f \cdot s(z, y_1, y_2)$ in the level-$Nq$ field and $\mathrm{red}\,\bigl(s(u, w_0, w_1)\bigr) \neq 0$.
--
--   This is a Hartogs-type statement for the three-coordinate integral model of $X_0(Nq)$ over $A$: a function integral for the second Gauss prolongation and regular along the whole strict second-kind residue disc above $\bar v$ is a quotient of polynomials in the coordinates $z, y_1, y_2$ whose denominator does not vanish under reduction at the chosen point. It is used to produce local chart data at strict second-kind places, via [`ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_chartData_of_isStrictSnd`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_chartData_of_isStrictSnd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ProlongationTupleSmoothPoint
import Definitions.Def_MDivRepresents

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingSnd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictSnd Q)
    (haff : IsAffineGeomPlace k N (P.reduceSnd Q))
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceSnd Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceSnd Q)
    (hgen : (P.reduceSnd Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jGeomGen k N) ∧
      (P.reduceSnd Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceSnd Q).evalAt (jNGeomGen k N))
    (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u : A) (w : Fin 2 → A)
    (htr : PlaceSpecialization.IsSndTriple (q := q) (P.reduceSnd Q) (red u) z y₁ y₂)
    (hu : 0 < Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)))
    (hw : ∀ j : Fin 2, 0 < Q.ord (![y₁, y₂] j -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w j : AlgebraicClosure ℚ)))
    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ∈ R.smoothLocalRingSnd (P.reduceSnd Q)) :
    ∃ p s : MvPolynomial (Option (Fin 2)) A,
      PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) p =
        f * PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) s ∧
      red (MvPolynomial.eval (fun o => Option.elim o u w) s) ≠ 0 := by sorry
