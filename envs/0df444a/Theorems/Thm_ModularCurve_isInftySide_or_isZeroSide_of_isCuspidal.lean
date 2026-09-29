-- Prove2me | Theorems.Thm_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal
-- name    : ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/664c9726-7acf-58a4-b2ea-1653cd1f2c89
-- title:
--   Cuspidal places of X₀(q): the ∞/0 dichotomy
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Fix also modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions), a proof `hKr` that $\Phi$ reduced modulo $q$ equals $(C X^q - X)(C X - X^q)$, and proofs `hα`, `hβ` that the two degeneracy embeddings of the level-$1$ into the level-$q$ modular function field over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation datum of level $1$ for these choices, that is, a map $\mathrm{sp}$ from places of the level-$1$ modular function field over $\overline{\mathbb Q}$ to places of the corresponding field over $k$ together with a homomorphism on degree-zero divisor class groups, subject to the compatibility conditions relating the order of vanishing of $j$-coordinates minus constants in $A$ to their reductions. Let $W$ be a place of the modular function field of level $1 \cdot q$ over $\overline{\mathbb Q}$, and assume $P$-cuspidality of $W$: for every $a \in A$ one has $\mathrm{ord}_W(\mathtt{jFun} - a) \le 0$, so the $j$-coordinate takes no $A$-integral value at $W$. The conclusion is a disjunction. Either $W$ is on the $\infty$-side, i.e. it is $P$-cuspidal in the above sense and there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ such that the cusp parameter `tInfty` lies in the valuation ring of $W$ with residue the image of $\tau$; or $W$ is on the $0$-side, i.e. the predicate `IsCuspidal'` holds for $P$ and $W$ and there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ such that the other cusp parameter `tZero` lies in the valuation ring of $W$ with residue the image of $\tau$.
--
--   This is the cusp (canonical-subgroup) dichotomy for $X_0(q)$ in the formulation used here: a point at which $j$ is not integral over $A$ lies in one of the two standard charts around the cusps, distinguished by the parameter $j_q/j^q$ or $j/j_q^q$ having residue $1$. It is obtained from Kronecker's congruence for the modular equation together with a root-size estimate, and is used to set up the two charts for the multiplicative covering and the level-one prolongation pairs, and is transported to the Jacobian-level specialisation datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal W) :
    P.IsInftySide W ∨ P.IsZeroSide W := by sorry
