-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_localSemicontinuitySnd_of_localSemicontinuityFst
-- name    : ModularCurve.PlaceSpecialization.localSemicontinuitySnd_of_localSemicontinuityFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/43113eb0-6f55-5ed2-b452-602115244312
-- title:
--   Local semicontinuity for the second component from the first
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a natural number $N \neq 0$, a field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, modular polynomial data `data` at level $q$ satisfying the Kronecker congruence `hKr` (the reduction mod $q$ of the bivariate modular polynomial factors as $(C(X)^q - X)(C(X) - X^q)$), and the hypotheses $h\alpha$, $h\beta$ that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` from the level-$N$ to the level-$Nq$ function field over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a `PlaceSpecialization` for these data, $R$ a `ProlongationTuple` over $P$, and assume $q \nmid N$. Write $\varphi$ for `frobOnPlacesGeomLevel k N data hKr`, the Frobenius map on places of `modularFunctionFieldC k N`. The hypothesis `hfst` asserts: for every $f$ in the level-$Nq$ function field `modularFunctionFieldBar (N * q)` lying in both valuation subrings `R.R₁.integers` and `R.R₂.integers` with both residues `R.R₁.residue` and `R.R₂.residue` non-zero, for every divisor $D$ on the level-$Nq$ field with $D(W) = \operatorname{ord}_W f$ at every place $W$, and for every place $v$ of `modularFunctionFieldC k N` with $\varphi(\varphi(v)) \neq v$ such that $D(W) \geq 0$ whenever `P.IsStrictFst W` (that is, $\varphi(\mathrm{red}_1 W) = \mathrm{red}_2 W$ and $\varphi^2(\mathrm{red}_1 W) \neq \mathrm{red}_1 W$) and $\mathrm{red}_1 W = v$, the value at $v$ of the pushforward along $\mathrm{red}_1 =$ `P.reduceFst` of the restriction of $D$ to the places satisfying `IsStrictFst` is at most $\operatorname{ord}_v$ of the image `R.residue₁ ⟨f, h₁⟩` in `modularFunctionFieldC k N`. The conclusion is the same assertion with the roles of the two components interchanged: `IsStrictSnd` (that is, $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ and $\varphi^2(\mathrm{red}_2 W) \neq \mathrm{red}_2 W$), pushforward along $\mathrm{red}_2 =$ `P.reduceSnd` of the restriction of $D$ to those places, and $\operatorname{ord}_u$ of `R.residue₂ ⟨f, h₂⟩`, for every place $u$ with $\varphi(\varphi(u)) \neq u$ at which $D$ is non-negative on the places of the second kind above $u$.
--
--   This is the symmetry step in the local semicontinuity estimate for the reduction of divisors on $X_0(Nq)$ in characteristic $q$: the clause for the second component of the special fibre is deduced from the clause for the first by transport along the partial Atkin–Lehner involution $w_q$, which exchanges the two components. It is used by [`ModularCurve.PlaceSpecialization.localSemicontinuity_of_reducesDivisors_of_hasCoordinates_of_hasCharts`](thm.html#ModularCurve.PlaceSpecialization.localSemicontinuity_of_reducesDivisors_of_hasCoordinates_of_hasCharts), where only the first-component estimate has to be established.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_localSemicontinuitySnd_of_localSemicontinuityFst.lean

import Definitions.Def_ModularCurve_ChartSemicontinuity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.localSemicontinuitySnd_of_localSemicontinuityFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N)
    (hfst : ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) →
        ∀ v : Place k (modularFunctionFieldC k N),
          frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
          (∀ W, P.IsStrictFst W → P.reduceFst W = v → 0 ≤ D W) →
          Finsupp.mapDomain P.reduceFst (P.fstDiv D) v ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) →
        ∀ u : Place k (modularFunctionFieldC k N),
          frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr u) ≠ u →
          (∀ W, P.IsStrictSnd W → P.reduceSnd W = u → 0 ≤ D W) →
          Finsupp.mapDomain P.reduceSnd (P.sndDiv D) u ≤ u.ord (R.residue₂ ⟨f, h₂⟩) := by sorry
