-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/101ee713-2721-5822-b7e5-0b75bcf2ca29
-- title:
--   Integrality at the second prolongation for functions with poles only at ∞̄
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} \colon A \to k$. Let `data` be modular polynomial data for $q$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ with $\Phi(j, j_q) = 0$, let `hKr` be the Kronecker congruence asserting that $\Phi$ reduced modulo $q$ equals $(X^q - Y)(X - Y^q)$, and let `hα`, `hβ` assert that the Hecke $\alpha$- and $\beta$-maps at level $1$ and prime $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place-specialisation datum `PlaceSpecialization A q 1 data hKr k red hα hβ` and let $R$ be a level-one prolongation pair for $P$; in particular $R$ provides two regular prolongations $R_1$, $R_2$ of $A$ to the field $F = \overline{\mathbb Q}(X_0(1\cdot q))$ (the base change to $\overline{\mathbb Q}$ of the full modular function field of level $1\cdot q$, realised inside Laurent series), each with residue map onto the full level-one modular function field over the residue field of $A$, and these are interchanged by the Fricke involution in the sense that $f \in R_2.\mathrm{integers}$ if and only if the Fricke involute of $f$ lies in $R_1.\mathrm{integers}$. Let $G \in F$ satisfy $0 \le \operatorname{ord}_W(G)$ for every place $W$ of $F$ over $\overline{\mathbb Q}$ with $W \ne \bar\infty$, where $\operatorname{ord}_W$ is minus the logarithm of the associated $\mathbb Z^{m0}$-valued adic valuation, so that $G$ has no pole away from the cusp $\bar\infty$. The conclusion is that if $G$ lies in the valuation subring $R_1.\mathrm{integers}$, then $G$ lies in $R_2.\mathrm{integers}$.
--
--   This is the valuation-theoretic form of the statement that a function regular outside the cusp $\bar\infty$ which is regular at the generic point of the component $C_\infty$ of the reduction of $X_0(q)$ at $q$ is also regular at the generic point of the component $C_0$, the underlying reason being that the relevant line bundle has degree $0$ on $C_0$. It is used in the proof of [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.padicValRat_coeff_frickeInvolutionFull_nonneg`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.padicValRat_coeff_frickeInvolutionFull_nonneg), towards control of the $q$-adic size of the $q$-expansion coefficients of Fricke involutes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} [IsAlgClosed k] (R : P.LevelOneProlongationPair)
    (G : ↥(modularFunctionFieldBar (1 * q)))
    (hG : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W ≠ cuspInftyBar (1 * q) → 0 ≤ W.ord G)
    (h₁ : G ∈ R.R₁.integers) :
    G ∈ R.R₂.integers := by sorry
