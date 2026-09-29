-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawFst_oneSided_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.divisorLawFst_oneSided_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/12ff1a92-1518-5c76-99cd-1355f176c396
-- title:
--   One-sided first divisor law at level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with modular polynomial data `data` for $q$ and a hypothesis `hKr` that the bivariate reduction mod $q$ of `data.Φ` equals $(C X^{q} - X)(C X - X^{q})$, and hypotheses `hα`, `hβ` that the two Hecke maps `heckeAlphaBar`, `heckeBetaBar` from level $1$ to level $1\cdot q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation for these data, carrying in particular a map `P.sp` from places of the level-$1$ function field over $\overline{\mathbb Q}$ to places of `modularFunctionFieldC k 1`, and let $R$ be a prolongation tuple over $P$, with `hmodel` the assumption that $R$ satisfies the four laws `R.DivisorLawFst`, `R.DivisorLawSnd`, `R.CuspLawInfty`, `R.CuspLawZero` constituting `IsModel`. The assertion is: for every $f$ in `modularFunctionFieldBar (1 * q)` lying in `R.R₁.integers` whose residue `R.R₁.residue ⟨f, h₁⟩` is non-zero, every divisor $D$ on places of that field with $D(W) = W.\mathrm{ord}\,f$ for all $W$, and every place $v$ of `modularFunctionFieldC k 1` over $k$ that is not fixed by the square of `frobOnPlacesGeomLevel k 1 data hKr`, the pushforward along `P.reduceFst` (restriction of a place along `heckeAlphaBar`, followed by `P.sp`) of the restriction of $D$ to those $W$ with `P.IsStrictFst W`, namely those satisfying $\mathrm{Frob}(\mathrm{reduceFst}\,W) = \mathrm{reduceSnd}\,W$ and $\mathrm{Frob}^2(\mathrm{reduceFst}\,W) \neq \mathrm{reduceFst}\,W$, takes at $v$ the value $v.\mathrm{ord}\,(R.\mathrm{residue}_1 \langle f, h_1\rangle)$.
--
--   This is the first-side divisor law for a model prolongation tuple, specialised to auxiliary level $N = 1$ (so that the ambient modular function fields are those of level $1 \cdot q$ and no coprimality hypothesis is needed): orders of the residue of an integral function at a place of the characteristic-$q$ curve not fixed by the square of Frobenius are computed by pushing forward the divisor of the function along the first reduction map. It is used in the level-one study of good divisors and of values of functions on the first smooth locus, and in the construction of elements of the first ring of integers attached to admissible divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawFst_oneSided_levelOne.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve

open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.divisorLawFst_oneSided_levelOne {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) (hmodel : R.IsModel) :
    ∀ (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        (∀ W, D W = W.ord f) →
        ∀ v : Place k (modularFunctionFieldC k 1),
          frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v →
          Finsupp.mapDomain P.reduceFst (D.filter P.IsStrictFst) v
            = v.ord (R.residue₁ ⟨f, h₁⟩) := by sorry
