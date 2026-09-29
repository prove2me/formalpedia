-- Prove2me | Theorems.Thm_ModularCurve_exists_constantReduction_chartData_of_isEmbBasis
-- name    : ModularCurve.exists_constantReduction_chartData_of_isEmbBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/5064eca0-7f2d-50e3-8f2c-29262ce78d9c
-- title:
--   Good constant reduction of the embedded modular curve, with charts
-- statement:
--   Let $N\ge 1$, let $r\in\mathbb N$ and let $s:\mathrm{Fin}\,r\to F_N:=$ `modularFunctionFieldBar N` (the base change to $\overline{\mathbb Q}$ of the full level-$N$ modular function field, inside Laurent series over $\overline{\mathbb Q}$) satisfy `IsEmbBasis N s`: the $s_i$ are linearly independent over $\overline{\mathbb Q}$ and span the Riemann–Roch space of $E:=$ `embDivisor N` $=(\mathrm{embDegree}\,N)\cdot\bar\infty$. Then there is a finite set $S$ of natural numbers, all prime, such that for every valuation subring $A\subset\overline{\mathbb Q}$ and every prime $\ell\notin S$ with $\ell$ a nonunit of $A$ there exist a field $\bar F$ that is an algebra over the residue field $k_A$ of $A$, a `ConstantReduction` $R$ of $F_N$ along $A$ with values in $\bar F$ (a valuation subring $R.\mathrm{integers}\subset F_N$, a surjective residue map onto $\bar F$ with kernel the maximal ideal, inducing $A\to k_A$, together with a map $P\mapsto\bar P$ on places preserving degrees and pushing forward divisors of functions), a proof that every $s_i$ lies in $R.\mathrm{integers}$, and two maps $c,i$ from places of $\bar F/k_A$ to $\mathrm{Fin}\,r$, such that: $R$ is good, i.e. the genus of $\bar F/k_A$ equals that of $F_N/\overline{\mathbb Q}$; every place $P$ of $F_N/\overline{\mathbb Q}$ and its reduction $\bar P$ are rational (the structure map to the residue field is surjective); for every $P$, the residue $\overline{s_{c(\bar P)}}$ is nonzero and $\mathrm{ord}_{\bar P}\,\overline{s_{c(\bar P)}}=-(R_*E)(\bar P)$, where $R_*E$ is the pushforward of $E$ along $P\mapsto\bar P$; for every $P$, provided $s_{i(\bar P)}s_{c(\bar P)}^{-1}\in R.\mathrm{integers}$, its residue $\bar\tau$ satisfies $\mathrm{ord}_{\bar P}(\bar\tau-\bar\tau(\bar P))=1$, the value $\bar\tau(\bar P)\in k_A$ being taken by `evalAt` and mapped into $\bar F$; and for all $P,P'$ with $\bar P'\neq\bar P$ such that also $\mathrm{ord}_{\bar P'}\,\overline{s_{c(\bar P)}}=-(R_*E)(\bar P')$, provided all quotients $s_js_{c(\bar P)}^{-1}$ lie in $R.\mathrm{integers}$, some index $j$ has $\overline{s_js_{c(\bar P)}^{-1}}$ taking different `evalAt` values at $\bar P$ and $\bar P'$.
--
--   This packages good reduction of the modular curve of level $N$, embedded by a basis of the Riemann–Roch space of the multiple $E$ of the cusp $\bar\infty$, in the language of constant reductions of function fields (Deuring, Igusa): outside a finite set of primes one obtains a genus-preserving reduction with a distinguished non-vanishing coordinate, a local uniformiser in the corresponding affine chart, and separation of reduced places by chart coordinates. It is the model-side input to the $\nu$-adic Jensen identities [`ModularCurve.JZero.jensen_good_at`](thm.html#ModularCurve.JZero.jensen_good_at) and [`ModularCurve.JZero.jensen_good_at_le`](thm.html#ModularCurve.JZero.jensen_good_at_le), isolated as a statement about reduction alone, with no heights.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_constantReduction_chartData_of_isEmbBasis.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_FinitePlaceLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_constantReduction_chartData_of_isEmbBasis (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ), ℓ.Prime → ℓ ∉ S →
      A.LiesOverPrime ℓ →
      ∃ (Fbar : Type) (_ : Field Fbar) (_ : Algebra (IsLocalRing.ResidueField A) Fbar)
        (R : ConstantReduction A (modularFunctionFieldBar N) Fbar) (hx : ∀ i, s i ∈ R.integers)
        (cQ iQ : Place (IsLocalRing.ResidueField A) Fbar → Fin r),
        R.IsGood ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.IsRational ∧ (R.placeMap P).IsRational) ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          R.residue ⟨s (cQ (R.placeMap P)), hx _⟩ ≠ 0 ∧
          (R.placeMap P).ord (R.residue ⟨s (cQ (R.placeMap P)), hx _⟩)
            = -(Finsupp.mapDomain R.placeMap (embDivisor N) (R.placeMap P))) ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          ∀ hmem : s (iQ (R.placeMap P)) * (s (cQ (R.placeMap P)))⁻¹ ∈ R.integers,
          (R.placeMap P).ord (R.residue ⟨_, hmem⟩
            - algebraMap (IsLocalRing.ResidueField A) Fbar ((R.placeMap P).evalAt (R.residue ⟨_, hmem⟩))) = 1) ∧
        (∀ P P' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.placeMap P' ≠ R.placeMap P →
          (R.placeMap P').ord (R.residue ⟨s (cQ (R.placeMap P)), hx _⟩)
            = -(Finsupp.mapDomain R.placeMap (embDivisor N) (R.placeMap P')) →
          ∀ hmem : ∀ j, s j * (s (cQ (R.placeMap P)))⁻¹ ∈ R.integers,
          ∃ j, (R.placeMap P).evalAt (R.residue ⟨_, hmem j⟩) ≠ (R.placeMap P').evalAt (R.residue ⟨_, hmem j⟩)) := by sorry
