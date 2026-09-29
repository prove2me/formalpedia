-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_isStrictFst_and_smul_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/775206c3-2307-5c28-978c-dc82057e3fda
-- title:
--   Existence of an inertia-fixed strict place avoiding W
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the $q$-expansion pair) satisfying the Kronecker congruence `hKr`, namely that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, together with the hypotheses $\mathtt{h\alpha}$, $\mathtt{h\beta}$ that the Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $N$ and prime $q$ are integral ring homomorphisms. Let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$, with $k$ algebraically closed, $q \nmid N$, and $R$ satisfying `IsModel`, i.e. the conjunction of its two divisor laws and its cusp laws at $\infty$ and at $0$. Let $W$ be a finite set of places of the geometric level-$N$ function field $\mathrm{modularFunctionFieldC}\ k\ N$, all of them supersingular, i.e. lying in `ssPlaces q N k`. Then there is a place $V_0$ of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$ (a valuation subring containing $\overline{\mathbb{Q}}$, proper, and a principal ideal ring) such that: $P.\mathrm{IsStrictFst}\ V_0$ holds, i.e. the geometric-level Frobenius takes $P.\mathrm{reduceFst}\ V_0$ to $P.\mathrm{reduceSnd}\ V_0$ while its square does not fix $P.\mathrm{reduceFst}\ V_0$; every $\sigma$ in the inertia subgroup of $A$ inside $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ fixes $V_0$ under the arithmetic Galois action on the level-$Nq$ field; and $P.\mathrm{reduceFst}\ V_0$, the specialisation under $P.\mathrm{sp}$ of the restriction of $V_0$ along $\overline{\alpha}$, does not lie in $W$.
--
--   This is the existence step for an unramified place of the level-$Nq$ function field lying over a smooth ordinary point of the first component of the special fibre at $q$, chosen outside a prescribed finite set of supersingular points and fixed by inertia; algebraic closedness of $k$ is essential, since over $\mathbb{F}_{q^2}$ every place would be fixed by the square of Frobenius. It feeds the construction of the depth and comparison laws for prolongation tuples and the assembly of the full list of laws at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_isStrictFst_and_smul_eq_self.lean

import Definitions.Def_ModularCurve_NodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_isStrictFst_and_smul_eq_self
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k) :
    ∃ V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.IsStrictFst V₀ ∧
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V₀ = V₀) ∧
      P.reduceFst V₀ ∉ W := by sorry
