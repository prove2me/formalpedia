-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq
-- name    : ModularCurve.PlaceSpecialization.reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/0b3c7dcb-bb8d-50e5-bfc8-7500f5dc2c69
-- title:
--   Places above a supersingular j-invariant reduce to supersingular places
-- statement:
--   Fix $N \geq 1$ and a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, and an algebraically closed field $k$ of characteristic $q$ such that the subfield $\mathrm{modularFunctionFieldC}\ k\ N \subseteq k((q))$ generated over $k$ by the $q$-expansions $j$ and $j(q^N)$ is a curve over $k$ in the sense of `IsCurveOver` (principal divisors exist, every place has residue field finite over $k$, and the differentials are free of rank one); fix a ring homomorphism $\mathrm{red} \colon A \to k$, a `ModularPolynomialData` $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j(q^q))$) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \bmod q$, integrality hypotheses $h\alpha, h\beta$ for the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$, and a `PlaceSpecialization` $P$ for these data, whose component `sp` maps places of $\mathrm{modularFunctionFieldBar}\ N$ to places of $\mathrm{modularFunctionFieldC}\ k\ N$. Assume the tower inclusion `towerInclBar` from level $1 \cdot q$ to level $N \cdot q$ is integral. Let $a \in k$ lie in $\mathrm{ssJSet}\ q\ k$, i.e. every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero affine point killed by $q$. Let $V'$ be a place of $\mathrm{modularFunctionFieldBar}\ (1 \cdot q)$ over $\overline{\mathbb{Q}}$ for which there is $x \in A$ with $\mathrm{red}(x) = a$ and $\mathrm{ord}_{V'}(j - x) > 0$, where $j$ is `jFun 1 q` and $\mathrm{ord}$ is minus the logarithm of the associated discrete valuation. Then for every place $V$ of $\mathrm{modularFunctionFieldBar}\ (N \cdot q)$ whose restriction along the tower inclusion is $V'$, the place $P.\mathrm{reduceFst}\ V$, namely the image under `sp` of the restriction of $V$ along `heckeAlphaBar`, lies in $\mathrm{ssPlaces}\ q\ N\ k$ — it is rational, satisfies the predicate `IsAffineGeomPlace`, and its value at the generator `jGeomGen k N` lies in $\mathrm{ssJSet}\ q\ k$ — and moreover that value equals $a$.
--
--   This is the statement that the supersingular points of the special fibre at $q$ of the modular curve of level $\Gamma_0(Nq)$ lie above supersingular points at level $N$: a place of the level-$Nq$ function field centred, after restriction to level $q$, at a point where $j$ specialises to a supersingular invariant $a$ reduces under the first degeneracy map to a supersingular place of the level-$N$ fibre with $j$-value $a$. It is used in the case analysis distinguishing ordinary from supersingular reductions, where a place of the level-$N$ fibre fixed by the reduction of the first degeneracy map is shown to carry a value of a modular unit or of its Atkin–Lehner twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DegeneracyTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.reduceFst_mem_ssPlaces_of_restrictAlong_towerInclBar_eq
    {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    [IsCurveOver k ↥(modularFunctionFieldC k N)] {red : ↥A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (hι : (towerInclBar (AlgebraicClosure ℚ)
      (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q)).toRingHom.IsIntegral)
    (a : k) (hss : a ∈ ssJSet q k)
    (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hVj : ∃ x : A, red x = a ∧
      0 < V'.ord (jFun 1 q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
        (x : AlgebraicClosure ℚ)))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : V.restrictAlong (towerInclBar (AlgebraicClosure ℚ)
      (mul_dvd_mul (one_dvd N) (dvd_refl q) : 1 * q ∣ N * q)) hι = V') :
    P.reduceFst V ∈ ssPlaces q N k ∧ (P.reduceFst V).evalAt (jGeomGen k N) = a := by sorry
