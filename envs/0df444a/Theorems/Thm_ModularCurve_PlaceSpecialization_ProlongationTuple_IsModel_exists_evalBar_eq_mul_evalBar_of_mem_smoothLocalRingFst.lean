-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingFst
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/75815892-ed37-5714-bcf2-5aaaa3af1bf3
-- title:
--   Local quotient form at a smooth strict first-kind point
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \ge 1$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, a modular polynomial datum `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions of $j$) satisfying the Kronecker congruence $\overline{\Phi} = (Y^q - X)(Y - X^q)$ over $\mathbb{F}_q$, integrality hypotheses $h\alpha$, $h\beta$ for the two degeneracy embeddings from level $N$ to level $Nq$, and a place specialisation $P$ from places of $\overline{\mathbb{Q}}(X_0(N))$ to places of `modularFunctionFieldC k N`, with $q \nmid N$. Let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k`, and let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), `RegularityLaw W`, `NodeValueLaw W` and `OrderLawFixed`. Let $Q$ be a place of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$ which is strict of the first kind for $P$, i.e. the geometric Frobenius sends $P.\mathrm{reduceFst}\,Q$ to $P.\mathrm{reduceSnd}\,Q$ while its square does not fix $P.\mathrm{reduceFst}\,Q$. Assume $\bar v := P.\mathrm{reduceFst}\,Q$ is affine geometric (both `jGeomGen k N` and `jNGeomGen k N` lie in its valuation ring), that some $c \in k \times k$ is a centre of $\bar v$ (both coordinates have positive order at $\bar v$ after subtraction) and that $\bar v$ is the unique place with that centre, and that the values of `jGeomGen k N` and `jNGeomGen k N` at $\bar v$ are both moved by $x \mapsto x^{q^2}$. Let $z, y_1, y_2$ in `modularFunctionFieldBar (N * q)`, $u \in A$ and $w : \mathrm{Fin}\,2 \to A$ be such that $(z; y_1, y_2)$ is a first-kind triple at $\bar v$ with value $\mathrm{red}\,u$ — either $(j; j_N, j_{Nq})$ with $\mathrm{ord}_{\bar v}(\mathrm{jGeomGen} - \mathrm{red}\,u) = 1$, or $(j_N; j, j_{Nq})$ with $\mathrm{ord}_{\bar v}(\mathrm{jNGeomGen} - \mathrm{red}\,u) = 1$ — and such that $\mathrm{ord}_Q(z - u) > 0$ and $\mathrm{ord}_Q(y_j - w_j) > 0$ for $j = 0, 1$. Then for every $f$ in $R.\mathrm{smoothLocalRingFst}\,\bar v$, that is, every $f$ lying in the valuation ring $R.R_1.\mathrm{integers}$ and in the valuation ring of every strict first-kind place whose first reduction is $\bar v$, there exist polynomials $p, s$ in three variables indexed by `Option (Fin 2)` with coefficients in $A$ such that $p(z, y_1, y_2) = f \cdot s(z, y_1, y_2)$ in `modularFunctionFieldBar (N * q)` and $\mathrm{red}\bigl(s(u, w_0, w_1)\bigr) \ne 0$.
--
--   This is the Hartogs-type local statement for the three-coordinate integral model of $X_0(Nq)$ over $A$: a function integral for the first Gauss prolongation and regular on the whole strict first-kind residue disc above $\bar v$ is a quotient of two polynomials in the coordinates $z, y_1, y_2$ whose denominator does not vanish at the reduced point. It feeds the construction of chart data at strict first-kind places, `exists_chartData_of_isStrictFst`, and rests on the corresponding statements for the integers of the prolongation and for the place specialisation alone.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingFst.lean

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

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_evalBar_eq_mul_evalBar_of_mem_smoothLocalRingFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    {W : Finset (Place k ↥(modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W)
    (hO : R.OrderLawFixed)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hQ : P.IsStrictFst Q)
    (haff : IsAffineGeomPlace k N (P.reduceFst Q))
    (hsm : ∃ c : k × k, IsCentreOf k N c (P.reduceFst Q) ∧
      ∀ v' : Place k ↥(modularFunctionFieldC k N), IsCentreOf k N c v' → v' = P.reduceFst Q)
    (hgen : (P.reduceFst Q).evalAt (jGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst Q).evalAt (jGeomGen k N) ∧
      (P.reduceFst Q).evalAt (jNGeomGen k N) ^ (q ^ 2) ≠ (P.reduceFst Q).evalAt (jNGeomGen k N))
    (z y₁ y₂ : ↥(modularFunctionFieldBar (N * q))) (u : A) (w : Fin 2 → A)
    (htr : PlaceSpecialization.IsFstTriple (q := q) (P.reduceFst Q) (red u) z y₁ y₂)
    (hu : 0 < Q.ord (z - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (u : AlgebraicClosure ℚ)))
    (hw : ∀ j : Fin 2, 0 < Q.ord (![y₁, y₂] j -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (w j : AlgebraicClosure ℚ)))
    (f : ↥(modularFunctionFieldBar (N * q))) (hf : f ∈ R.smoothLocalRingFst (P.reduceFst Q)) :
    ∃ p s : MvPolynomial (Option (Fin 2)) A,
      PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) p =
        f * PlaceSpecialization.evalBar N q (fun o => Option.elim o z ![y₁, y₂]) s ∧
      red (MvPolynomial.eval (fun o => Option.elim o u w) s) ≠ 0 := by sorry
