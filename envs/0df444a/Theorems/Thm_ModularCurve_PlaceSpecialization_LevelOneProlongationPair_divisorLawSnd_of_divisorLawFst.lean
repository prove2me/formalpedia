-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawSnd_of_divisorLawFst
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawSnd_of_divisorLawFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/d81fba46-888d-5432-9cb6-a46431afcabf
-- title:
--   Fricke transport of the level-one divisor law
-- statement:
--   Let $q$ be a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $k$ a field of characteristic $q$ and $red : A \to k$ a ring homomorphism. Let `data` be a `ModularPolynomialData q`, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, and let `hKr` be the Kronecker congruence for it, namely that the bivariate reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)\,(C(X) - X^q)$; let `hα`, `hβ` assert that the ring homomorphisms underlying `heckeAlphaBar` and `heckeBetaBar` for $(\overline{\mathbb Q}, 1, q)$ are integral. Let $P$ be a `PlaceSpecialization` for these data and $R$ a `LevelOneProlongationPair` for $P$: two regular prolongations $R_1, R_2$ of $A$ to `modularFunctionFieldBar (1*q)` with residue fields in `modularFunctionFieldFullC (ResidueField A) 1`, a compatible reduction `redBar` and embedding `ι` into `modularFunctionFieldC k 1`, where $R_2$ is the Fricke transport of $R_1$ in the sense that $f \in R_2$.integers iff `frickeInvolutionBar (1*q) f` $\in R_1$.integers and $R_2$'s residue of $f$ is $R_1$'s residue of `frickeInvolutionBar (1*q) f`. Assume `R.DivisorLawFst`: for every $f$ in the integers of both $R_1$ and $R_2$ with both residues nonzero, every divisor $D$ on the places of `modularFunctionFieldBar (1*q)` over $\overline{\mathbb Q}$ with $D(W) = \operatorname{ord}_W f$ for all $W$, and every place $v$ of `modularFunctionFieldC k 1` not fixed by the square of `frobOnPlacesGeomLevel k 1 data hKr`, the pushforward along `P.redFst` of the restriction of $D$ to the places satisfying `P.IsStrictTypeOne`, evaluated at $v$, equals $\operatorname{ord}_v$ of `R.residue₁ ⟨f, h₁⟩`. Then the same holds with `P.redSnd`, `P.IsStrictTypeTwo` and `R.residue₂ ⟨f, h₂⟩` in place of `P.redFst`, `P.IsStrictTypeOne` and `R.residue₁ ⟨f, h₁⟩` (`R.DivisorLawSnd`).
--
--   The two divisor laws express, for the special fibre of the modular curve of level $q$ at a place of residue characteristic $q$, that the divisor of a common unit on each of the two components of the special fibre is computed by summing orders at the places of the generic fibre reducing to a given point. The statement says the second law is a formal consequence of the first, and it is used in the construction of models and in the production of common units with prescribed poles along the components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawSnd_of_divisorLawFst.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawSnd_of_divisorLawFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : PlaceSpecialization.LevelOneProlongationPair P)
    (hF : R.DivisorLawFst) : R.DivisorLawSnd := by sorry
