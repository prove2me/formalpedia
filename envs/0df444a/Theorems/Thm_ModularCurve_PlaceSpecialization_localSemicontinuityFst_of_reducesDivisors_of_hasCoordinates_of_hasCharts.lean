-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_localSemicontinuityFst_of_reducesDivisors_of_hasCoordinates_of_hasCharts
-- name    : ModularCurve.PlaceSpecialization.localSemicontinuityFst_of_reducesDivisors_of_hasCoordinates_of_hasCharts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/88e6908c-18f2-5aff-89a7-2383ba49198a
-- title:
--   Local semicontinuity at first-kind places over a non-fixed place
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a level $N \neq 0$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data `data` for $q$ together with a proof `hKr` that its bivariate reduction mod $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and integrality hypotheses $h\alpha$, $h\beta$ saying that the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$N$ into the level-$Nq$ geometric modular function field over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialization for these data, sending places of `modularFunctionFieldBar N` to places of `modularFunctionFieldC k N`, and let $R$ be a prolongation tuple over $P$, with its two regular prolongations $R_1$, $R_2$ of $A$ to the level-$Nq$ field and residue map `R.residue₁` into `modularFunctionFieldC k N`. Assume $q \nmid N$; that $P$ reduces divisors (`ReducesDivisors`: for a level-$N$ function whose reduction is a non-zero element of `modularFunctionFieldC k N`, the pushforward along `P.sp` of its divisor is the order divisor of that reduction); that $P$ has coordinates (`HasCoordinates`: every place of `modularFunctionFieldC k N` admits a level-$N$ function whose reduction, minus a constant, has order exactly $1$ there, compatibly with all places above it); and that $R$ has charts (`HasCharts`: every place $v$ of `modularFunctionFieldC k N` with $\varphi(\varphi(v)) \neq v$, where $\varphi$ denotes `frobOnPlacesGeomLevel k N data hKr`, carries a set $S$ of level-$Nq$ functions satisfying `IsChartAt R v S`). The conclusion is: for every $f$ in the level-$Nq$ field lying in the valuation subrings $R_1$.integers and $R_2$.integers with both residues $R_1$.residue$(f)$ and $R_2$.residue$(f)$ non-zero, for every divisor $D$ on the places of the level-$Nq$ field with $D(W) = \operatorname{ord}_W(f)$ for all $W$, and for every place $v$ of `modularFunctionFieldC k N` with $\varphi(\varphi(v)) \neq v$ such that $D(W) \ge 0$ for every $W$ with `P.IsStrictFst W` and `P.reduceFst W = v`, the value at $v$ of the pushforward along `P.reduceFst` of the restriction of $D$ to the places satisfying `P.IsStrictFst` — that is, the sum of $D(W)$ over places $W$ with $\varphi(\mathrm{red}_1 W) = \mathrm{red}_2 W$, $\varphi(\varphi(\mathrm{red}_1 W)) \neq \mathrm{red}_1 W$ and $\mathrm{red}_1 W = v$, where $\mathrm{red}_1$, $\mathrm{red}_2$ are the reductions along `heckeAlphaBar` and `heckeBetaBar` — is at most $\operatorname{ord}_v$ of `R.residue₁`$(f)$.
--
--   This is the semicontinuity inequality for the first of the two families of places of the level-$Nq$ field lying over a place of the level-$N$ fibre that is not fixed by the square of the geometric Frobenius on places, in the Deuring-style theory of reduction of divisors used to describe the fibre of $X_0(Nq)$ at $q$ as two copies of $X_0(N)$. It is the first half of the two-sided local semicontinuity statement and is cited by [`ModularCurve.PlaceSpecialization.localSemicontinuity_of_reducesDivisors_of_hasCoordinates_of_hasCharts`](thm.html#ModularCurve.PlaceSpecialization.localSemicontinuity_of_reducesDivisors_of_hasCoordinates_of_hasCharts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_localSemicontinuityFst_of_reducesDivisors_of_hasCoordinates_of_hasCharts.lean

import Definitions.Def_ModularCurve_ChartSemicontinuity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.localSemicontinuityFst_of_reducesDivisors_of_hasCoordinates_of_hasCharts
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N) (hsp : ReducesDivisors P) (hcoord : HasCoordinates P) (hchart : HasCharts R) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) →
        ∀ v : Place k (modularFunctionFieldC k N),
          frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
          (∀ W, P.IsStrictFst W → P.reduceFst W = v → 0 ≤ D W) →
          Finsupp.mapDomain P.reduceFst (P.fstDiv D) v ≤ v.ord (R.residue₁ ⟨f, h₁⟩) := by sorry
