-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isAlgClosed_of_level_of_not_dvd
-- name    : ModularCurve.PlaceSpecialization.isAlgClosed_of_level_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/6e445a71-a359-5dda-b67d-3dc633706bf9
-- title:
--   Algebraic closedness of the residue field at level prime to q
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ (the Lean `AlgebraicClosure ℚ`), a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Fix further a `ModularPolynomialData` for $q$, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ vanishing on the pair $(j, j_q)$ of $q$-expansions, together with a proof `hKr` of the Kronecker congruence, i.e. that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and proofs `hα`, `hβ` that the two degeneracy maps `heckeAlphaBar`, `heckeBetaBar` from the base change to $\overline{\mathbb{Q}}$ of the full level-$N$ modular function field into that of level $N q$ are integral ring homomorphisms. Assume $q \nmid N$, and assume given a term $P$ of the structure `PlaceSpecialization` for these data: a map `sp` from places of $\overline{\mathbb{Q}}$-modular function field of level $N$ to places of $k(j_{\bmod},\,j_{N,\bmod})$, a homomorphism on degree-zero divisor classes, and the axioms relating orders of the $j$- and $j_N$-coordinates before and after specialisation, including that $j$-integral points specialise to $\mathrm{red}(a)$ and poles to poles, and that every place of the characteristic-$q$ function field is `sp` of some place upstairs. Then $k$ is algebraically closed.
--
--   This is the level-$N$ form, under the assumption that the level is prime to the residue characteristic, of the statement that the residue field of a place specialisation of the modular curve is algebraically closed. It is used in the construction of prolongation tuples and in the analysis of the Frobenius action on places of the special fibre at geometric level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isAlgClosed_of_level_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.isAlgClosed_of_level_of_not_dvd
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ) : IsAlgClosed k := by sorry
