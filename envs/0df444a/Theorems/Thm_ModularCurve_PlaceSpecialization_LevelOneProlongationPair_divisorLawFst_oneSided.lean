-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst_oneSided
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawFst_oneSided
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/55dddc32-d256-5dd9-9ffb-e9685d0eba84
-- title:
--   One-sided first-branch divisor law off the φ²-fixed places
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$, a ring homomorphism $red : A \to k$, data $data$ consisting of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, together with the Kronecker congruence $hKr$ asserting that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and the hypotheses $h\alpha$, $h\beta$ that the two Hecke embeddings $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ of level $1$ and prime $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation of this data and $R$ a level-one prolongation pair for $P$, so in particular $R$ provides two regular prolongations $R_1, R_2$ of $A$ to the base-changed modular function field $\mathrm{modularFunctionFieldBar}(1\cdot q)$ with residues in the level-one function field over the residue field of $A$, interchanged by the Fricke involution, and a compatible embedding $\iota$ into $\mathrm{modularFunctionFieldC}\ k\ 1$. Let $f$ be an element of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ lying in the integers of $R_1$ and with nonzero residue there, and let $D$ be a divisor, i.e. a finitely supported integer-valued function on the places of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbb Q}$, such that $D(W) = \mathrm{ord}_W(f)$ for every place $W$, where $\mathrm{ord}$ is minus the logarithm of the adic valuation. Let $v$ be a place of $\mathrm{modularFunctionFieldC}\ k\ 1$ over $k$ with $\varphi(\varphi(v)) \neq v$, where $\varphi = \mathrm{frobOnPlacesGeomLevel}\ k\ 1\ data\ hKr$. Then the pushforward along $P.\mathrm{redFst}$ (restriction of a place along the $\alpha$-Hecke embedding followed by the specialisation map of $P$) of the restriction of $D$ to the places $W$ of strict type one — those with $\varphi(P.\mathrm{redFst}\,W) = P.\mathrm{redSnd}\,W$ and $\varphi(\varphi(P.\mathrm{redFst}\,W)) \neq P.\mathrm{redFst}\,W$ — takes at $v$ the value $\mathrm{ord}_v$ of the element $R.\mathrm{residue}_1\langle f, h_1\rangle$ of $\mathrm{modularFunctionFieldC}\ k\ 1$ attached by $R$ to $f$ at the first prolongation. Equivalently, the sum of $\mathrm{ord}_W(f)$ over the strict-type-one places $W$ with first reduction $v$ equals the order of the first residue of $f$ at $v$.
--
--   This is the one-sided form of the divisor law comparing the divisor of a function on the level-$q$ modular curve over $\overline{\mathbb Q}$ with the divisor of its residue on the first component of the mod-$q$ special fibre: only integrality and non-vanishing of the residue at the first prolongation are assumed, and the conclusion holds at every place of the level-one function field not fixed by the square of the geometric Frobenius on places, i.e. at points through which the second component does not pass. It feeds the construction and verification of the Deligne–Rapoport style model of the reduction, being used for the existence of values on the smooth locus of the first branch, for the chart supply on that branch, and, via Fricke transport, for the companion law on the second branch.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst_oneSided.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve
open Classical in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawFst_oneSided
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (hf : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f)
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v) :
    Finsupp.mapDomain P.redFst (D.filter P.IsStrictTypeOne) v = v.ord (R.residue₁ ⟨f, h₁⟩) := by sorry
