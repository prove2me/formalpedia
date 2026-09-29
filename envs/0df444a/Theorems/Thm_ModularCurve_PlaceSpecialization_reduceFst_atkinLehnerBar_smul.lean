-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
-- name    : ModularCurve.PlaceSpecialization.reduceFst_atkinLehnerBar_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/f419ff53-a753-5fd9-8190-d4712848b000
-- title:
--   Atkin–Lehner transport swaps the two reductions at q ∤ N
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a natural number $N \neq 0$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` consist of a monic polynomial $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, let `hKr` assert the Kronecker congruence that $\Phi$ reduced modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$ in the bivariate convention used, and let `hα`, `hβ` assert that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` of the level-$N$ modular function field over $\overline{\mathbb{Q}}$ into the level-$Nq$ one are integral ring maps. Let $P$ be a `PlaceSpecialization` for these data, whose component `sp` sends places of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ to places of `modularFunctionFieldC k N` over $k$, and assume $q \nmid N$. Then for every place $W$ of `modularFunctionFieldBar (N * q)` over $\overline{\mathbb{Q}}$ — that is, a proper valuation subring containing the image of $\overline{\mathbb{Q}}$ whose ideals are principal — one has $P.\mathrm{sp}$ of the restriction of $\mathrm{atkinLehnerBar}\,N\,q \cdot W$ along `heckeAlphaBar` equal to $P.\mathrm{sp}$ of the restriction of $W$ along `heckeBetaBar`; here $\mathrm{atkinLehnerBar}\,N\,q$ is the base change to $\overline{\mathbb{Q}}$ of the Atkin–Lehner involution `atkinLehnerInvolutionFull N q`, acting on places, and the two sides are by definition `P.reduceFst` and `P.reduceSnd`.
--
--   This is the compatibility of the Atkin–Lehner involution $w_q$ at a prime $q$ exactly dividing the level with the two degeneracy maps $X_0(Nq) \to X_0(N)$: transporting a place by $w_q$ interchanges the two readings of the special fibre. It is used throughout the analysis of glued specialisations and of models for the level-$Nq$ curve in residue characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.reduceFst_atkinLehnerBar_smul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    P.reduceFst (ProlongationTuple.atkinLehnerBar N q • W) = P.reduceSnd W := by sorry
