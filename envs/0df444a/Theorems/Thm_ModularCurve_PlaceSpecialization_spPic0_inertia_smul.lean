-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_inertia_smul
-- name    : ModularCurve.PlaceSpecialization.spPic0_inertia_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/33df208f-ee94-5ed9-a357-2334de1d5f24
-- title:
--   Inertia acts trivially on J₀(N) through a specialization packet
-- statement:
--   Fix a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, a prime $\ell$, a nonzero level $N$, a datum `data : ModularPolynomialData ℓ` (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(\ell)$ vanishing on the pair $(j(q), j(q^{\ell}))$), together with a proof `hKr` that $\Phi$ satisfies the Kronecker congruence, i.e. that its reduction modulo $\ell$ equals $(X^{\ell} - Y)(X - Y^{\ell})$ in the bivariate polynomial ring over $\mathbb{Z}/\ell$. Fix further a field $k$ of characteristic $\ell$, a ring homomorphism $\mathrm{red} : A \to k$, and hypotheses $h\alpha$, $h\beta$ asserting that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` of the base-changed modular function field of level $N$ into that of level $N\ell$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $S$ be a `PlaceSpecialization` packet for these data: in particular it provides a map `sp` on places of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ to places of `modularFunctionFieldC k N`, an additive map `spPic0` from $J_0(N) =$ `JZero N`, the degree-zero divisor class group of the level-$N$ modular function field over $\overline{\mathbb{Q}}$, to the degree-zero divisor class group of `modularFunctionFieldC k N`, and the compatibility fields of that structure. Let $\sigma$ be an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ belonging to `A.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ inside the decomposition subgroup of $A$. Then for every $x \in J_0(N)$ one has `S.spPic0 (σ • x) = S.spPic0 x`, the action being the arithmetic Galois action on $J_0(N)$.
--
--   This expresses, inside the chosen specialization packet, the statement that the reduction map to the special fibre kills the inertia action on the Jacobian of $X_0(N)$, the Galois-theoretic shadow of good reduction away from the level. It is used in the construction and comparison of fibre models and glued specializations, for instance by [`ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_decomposition_smul_eq_spPic0_smul`](thm.html#ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_decomposition_smul_eq_spPic0_smul) and by the existence statements for specializations at a prime of good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_spPic0_inertia_smul.lean

import Definitions.Def_ModularCurve_PlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.spPic0_inertia_smul {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ N : ℕ} [Fact ℓ.Prime] [NeZero N]
    {data : ModularPolynomialData ℓ} {hKr : KroneckerCongruence ℓ data}
    {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ}
    (S : PlaceSpecialization A ℓ N data hKr k red hα hβ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (x : JZero N) : S.spPic0 (σ • x) = S.spPic0 x := by sorry
