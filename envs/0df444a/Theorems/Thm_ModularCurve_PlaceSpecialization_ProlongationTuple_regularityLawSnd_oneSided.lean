-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.regularityLawSnd_oneSided
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/1162efe3-d2f9-57fa-8cfe-19f08e6e65af
-- title:
--   One-sided second-copy regularity at φ²-fixed ordinary places
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an integer $N \ge 1$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, data `data` consisting of a monic bivariate integral polynomial $\Phi$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions, together with the Kronecker congruence `hKr` asserting that the reduction of $\Phi$ modulo $q$ is $(C(X)^q - X)(C(X) - X^q)$, and the hypotheses `hα`, `hβ` that the two Hecke maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from level $N$ to level $Nq$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Assume $q \nmid N$. Let $P$ be a place specialisation of these data, let $W$ be a finite set of places of `modularFunctionFieldC k N` whose members are exactly the supersingular places `ssPlaces q N k`, and let $R$ be a prolongation tuple over $P$ satisfying the regularity law `R.RegularityLaw W`. Write $\varphi$ for `frobOnPlacesGeomLevel k N data hKr`. Then for every $f$ in `modularFunctionFieldBar (N * q)` lying in the integers of the second prolongation $R_2$, with nonzero residue there, and every place $v$ of `modularFunctionFieldC k N` such that $\varphi(\varphi(v)) = v$, such that $v$ is affine in the sense that both $\mathrm{jGeomGen}$ and $\mathrm{jNGeomGen}$ lie in the valuation subring of $v$, such that $v \notin W$, and such that $\mathrm{ord}_V(f) \ge 0$ for every place $V$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb Q}$ with $P.\mathrm{reduceFst}\,V = v$, one has $\mathrm{ord}_{\varphi(v)}(R.\mathrm{residue}_2(f)) \ge 0$, where $R.\mathrm{residue}_2(f)$ denotes the second-copy reduction of $f$ viewed in `modularFunctionFieldC k N`. Thus the second conjunct of the first clause of the regularity law is recovered while requiring only integrality of $f$ for the second prolongation, not for both.
--
--   This is the second-copy half of the pointwise regularity statement at the places of the level-$N$ special fibre fixed by the square of Frobenius and lying outside the supersingular locus; it strips from the regularity law the hypothesis that $f$ be integral for the first prolongation as well. It is used in the computation of the two divisors attached to an annulus datum at level $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.regularityLawSnd_oneSided {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    [DecidableEq k] (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (R : ProlongationTuple P) (hreg : R.RegularityLaw W) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₂ : f ∈ R.R₂.integers),
      R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
        v ∉ W →
        (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          P.reduceFst V = v → 0 ≤ V.ord f) →
        0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩) := by sorry
