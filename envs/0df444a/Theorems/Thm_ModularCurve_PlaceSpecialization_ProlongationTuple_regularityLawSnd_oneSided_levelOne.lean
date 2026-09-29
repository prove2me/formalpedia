-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.regularityLawSnd_oneSided_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/4300d41a-3260-523c-9934-bf55102eb95e
-- title:
--   Second-side one-sided regularity law, level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$, a ring homomorphism $\mathrm{red} : A \to k$, modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the $q$-division $j$-expansions), a proof `hKr` that the reduction of $\Phi$ modulo $q$ equals $(\,C X^q - X)(C X - X^q)$, and proofs `hα`, `hβ` that the two Hecke maps $\bar\alpha, \bar\beta$ at level $1$ and prime $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data, let $W$ be a finite set of places of `modularFunctionFieldC k 1` which, by `hW`, consists exactly of the members of `ssPlaces q 1 k`, let $R$ be a `ProlongationTuple` for $P$, with its two regular prolongations `R.R₁`, `R.R₂` of $A$ to `modularFunctionFieldBar (1 * q)`, and assume `hreg : R.RegularityLaw W`. The conclusion: for every $f$ in `modularFunctionFieldBar (1 * q)` lying in the integers of `R.R₂` whose `R.R₂`-residue is nonzero, and every place $v$ of `modularFunctionFieldC k 1` such that $\varphi(\varphi(v)) = v$ for $\varphi =$ `frobOnPlacesGeomLevel k 1 data hKr`, such that both $j$-generators `jGeomGen k 1` and `jNGeomGen k 1` lie in the valuation subring of $v$, such that $v \notin W$, and such that every place $V$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ with `P.reduceFst V = v` satisfies $\operatorname{ord}_V f \ge 0$, one has $\operatorname{ord}_{\varphi(v)}$ of the second residue `R.residue₂ ⟨f, h₂⟩` $\ge 0$, the order being read at $\varphi(v)$ in `modularFunctionFieldC k 1`. Thus this is the second conjunct of the first clause of `R.RegularityLaw W` at $N = 1$, with the hypothesis that $f$ lie in the integers of `R.R₁` removed and the extra hypothesis $v \notin W$ imposed.
--
--   This is the level-one regularity statement for the second Gauss prolongation: on the special fibre of $X_0(q)$, which at level one consists of two copies of the $j$-line meeting at the supersingular points $W$, a function integral for the second prolongation and with no pole over an ordinary, $\varphi^2$-fixed place $v$ has no pole at $\varphi(v)$ on the second copy. It feeds the constructions of component charts and annuli attached to models, and the associated divisor-class computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.regularityLawSnd_oneSided_levelOne {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q} [IsAlgClosed k]
    [DecidableEq k]
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hreg : R.RegularityLaw W) :
    ∀ (f : modularFunctionFieldBar (1 * q)) (h₂ : f ∈ R.R₂.integers),
      R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
        IsAffineGeomPlace k 1 v →
        v ∉ W →
        (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
          P.reduceFst V = v → 0 ≤ V.ord f) →
        0 ≤ (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨f, h₂⟩) := by sorry
