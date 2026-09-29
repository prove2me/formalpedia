-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_ord_add_sum_roots
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_ord_add_sum_roots
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/8ab80b47-43a8-502c-9dc4-8d43f192d046
-- title:
--   Value-indexed summed pencil law over the j-line
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix modular polynomial data for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$) together with a proof `hKr` that its reduction modulo $q$ is $(C X^q - X)(C X - X^q)$, and proofs $h\alpha$, $h\beta$ that the two degeneracy maps `heckeAlphaBar` and `heckeBetaBar` at level $1$ and prime $q$ are integral ring homomorphisms. Let $P$ be a place-specialization datum for these data and $R$ a level-one prolongation pair for $P$, with its two regular prolongations $R_1$, $R_2$ of the function field `modularFunctionFieldBar (1 * q)`. Let $f$ lie in the valuation rings of both $R_1$ and $R_2$, with nonzero residues in each, let $D$ be a divisor on the places of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ satisfying $D(W) = \operatorname{ord}_W f$ for every place $W$, and let $c_0 \in k$. Then the sum of $D$ over those places $W$ in its support for which some $a \in A$ has $\mathrm{red}(a) = c_0$ and $\operatorname{ord}_W(j - a) > 0$ (here $j$ is `PlaceSpecialization.jFun`, the $q$-expansion of $j$ viewed in the level-$(1 \cdot q)$ field, and $a$ is taken via the structure map of $\overline{\mathbb Q}$) equals $$\sum_{a \in \mathrm{roots}(X - C c_0)} \operatorname{ord}_{[a]}\bigl(R.\mathrm{residue}_1 f\bigr) \; + \sum_{b \in \mathrm{roots}(X^q - C c_0)} \operatorname{ord}_{[b]}\bigl(R.\mathrm{residue}_2 f\bigr),$$ the sums being over the distinct roots in $k$ of the indicated polynomials, $[c]$ denoting the place `charLGeomPlaceOfPoint k c` of the level-one modular function field over $k$ attached to the point $c$, and $R.\mathrm{residue}_1 f$, $R.\mathrm{residue}_2 f$ the images of $f$ in that field under the two prolongations. The first sum has the single term $a = c_0$.
--
--   This is the value-indexed form of the summed order law for a pencil on $X_0(q)$: it computes the total order of vanishing of $f$ along the fibre of the $j$-line above a point $c_0 \in k$ in terms of the orders of the two reductions of $f$ on the two branches produced by the Kronecker congruence modulo $q$, the first branch being the identity parametrisation $X$ and the second the $q$-power parametrisation $X^q$. It is used in the proof of [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_ord_pencil_eq`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_ord_pencil_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_sum_filter_value_eq_ord_add_sum_roots.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve Polynomial
open Classical in

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.sum_filter_value_eq_ord_add_sum_roots
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair) [DecidableEq k]
    (f : modularFunctionFieldBar (1 * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hu₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hu₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f) (c₀ : k) :
    (D.support.filter fun W => ∃ a : A, red a = c₀ ∧
        0 < W.ord (PlaceSpecialization.jFun (q := q)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))).sum D
      = (∑ a ∈ (X - C c₀ : k[X]).roots.toFinset, (charLGeomPlaceOfPoint k a).ord (R.residue₁ ⟨f, h₁⟩))
        + ∑ b ∈ (X ^ q - C c₀ : k[X]).roots.toFinset, (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨f, h₂⟩) := by sorry
