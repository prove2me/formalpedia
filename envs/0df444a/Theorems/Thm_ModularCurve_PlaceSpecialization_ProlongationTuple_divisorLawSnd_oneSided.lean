-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawSnd_oneSided
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.divisorLawSnd_oneSided
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/9038ac5c-0b81-5379-bff0-0d11c63d9b74
-- title:
--   One-sided second divisor law for prolongation tuples
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ (the algebraic closure of $\mathbb{Q}$), a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) satisfying the Kronecker congruence `hKr`, namely that the reduction of $\Phi$ modulo $q$ equals $(C X^{q} - X)(C X - X^{q})$, and assume the ring maps underlying `heckeAlphaBar` and `heckeBetaBar` at level $N$ and $q$ are integral (`hα`, `hβ`). Assume $q \nmid N$, let $P$ be a place specialisation `PlaceSpecialization A q N data hKr k red hα hβ`, let $R$ be a prolongation tuple over $P$, and assume `R.IsModel`, i.e. $R$ satisfies `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty` and `CuspLawZero`. The assertion is: for every $f$ in the base-changed modular function field `modularFunctionFieldBar (N * q)` inside $\overline{\mathbb{Q}}$-Laurent series, every witness $h_2$ that $f$ lies in the integers of $R.R_2$, with $R.R_2$-residue of $f$ nonzero, every divisor $D$ on the places of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$ with $D(W) = W.\mathrm{ord}(f)$ for all $W$, and every place $v$ of `modularFunctionFieldC k N` over $k$ with $\mathrm{Frob}(\mathrm{Frob}(v)) \ne v$ for the geometric-level Frobenius `frobOnPlacesGeomLevel`: the pushforward along `P.reduceSnd` of the part of $D$ supported on the places $W$ with `P.IsStrictSnd W` (that is, $P.\mathrm{reduceFst}(W) = \mathrm{Frob}(P.\mathrm{reduceSnd}(W))$ and $\mathrm{Frob}^2(P.\mathrm{reduceSnd}(W)) \ne P.\mathrm{reduceSnd}(W)$), evaluated at $v$, equals $v.\mathrm{ord}$ of `R.residue₂ ⟨f, h₂⟩`.
--
--   This is the one-sided (second-copy) form of the divisor pushforward law packaged in `IsModel`: it computes, at places of the geometric special fibre not fixed by the square of Frobenius, the multiplicity of the second reduction of the divisor of a function in terms of the order of its second residue. It is used downstream in the analysis of annulus data, in the description of the smooth local ring on the second component, and in scaling arguments producing functions with prescribed divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawSnd_oneSided.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve

open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.divisorLawSnd_oneSided {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₂ : f ∈ R.R₂.integers),
      R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) →
        ∀ v : Place k (modularFunctionFieldC k N),
          frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v →
          Finsupp.mapDomain P.reduceSnd (D.filter P.IsStrictSnd) v
            = v.ord (R.residue₂ ⟨f, h₂⟩) := by sorry
