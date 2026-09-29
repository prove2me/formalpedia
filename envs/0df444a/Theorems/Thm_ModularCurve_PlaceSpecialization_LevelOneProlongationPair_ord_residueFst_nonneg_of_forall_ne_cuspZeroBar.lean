-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residueFst_nonneg_of_forall_ne_cuspZeroBar
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ord_residueFst_nonneg_of_forall_ne_cuspZeroBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/a4c04b09-d303-5b5a-9c9b-f388300392da
-- title:
--   Regular first residue when poles are confined to ̄ 0
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ with decidable equality, and a ring homomorphism $\mathrm{red} : A \to k$. Fix further data of the level-$q$ modular polynomial, namely $\mathrm{data}$ consisting of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, a proof $hKr$ that the reduction of $\Phi$ modulo $q$ equals $(CX^q - X)(CX - X^q)$, and proofs $h\alpha$, $h\beta$ that the two Hecke maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ at level $1$ and prime $q$ are integral ring homomorphisms; let $P$ be a place specialisation for these data and $R$ a level-one prolongation pair for $P$, whose components include regular prolongations $R_1, R_2$ of $A$ inside the base-changed full modular function field $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbb Q}$, with residues in the geometric level-one field over the residue field of $A$, together with the comparison map $\iota$ to $\mathrm{modularFunctionFieldC}\,k\,1$. Let $f$ be an element of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ lying in the valuation subring $R_1.\mathrm{integers}$, with first residue $\mathrm{residue}_1(f) \neq 0$, lying also in $R_2.\mathrm{integers}$, and such that $0 \le \operatorname{ord}_W f$ for every place $W$ of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbb Q}$ other than $\mathrm{cuspZeroBar}(1\cdot q)$, the Fricke translate of the cusp at infinity; here a place is a proper valuation subring containing the base field whose ring is a principal ideal ring, and $\operatorname{ord}$ is minus the logarithm of its adic valuation. Then for every place $v$ of $\mathrm{modularFunctionFieldC}\,k\,1$ over $k$ one has $0 \le \operatorname{ord}_v \mathrm{residue}_1(f)$.
--
--   On the special fibre of $X_0(q)$ at $q$, with its two components meeting at the supersingular points, this says that a function integral on both components whose only pole upstairs is the cusp $\bar 0$ reduces to a function on the $\bar\infty$-component with no pole at all, i.e. its first residue is regular on the whole $\tilde\jmath$-line. It is the regularity input for [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residueFst_nonneg_of_forall_ne_cuspZeroBar.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ord_residueFst_nonneg_of_forall_ne_cuspZeroBar
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (hf : R.residue₁ ⟨f, h₁⟩ ≠ 0)
    (h₂ : f ∈ R.R₂.integers)
    (hpoles : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      W ≠ cuspZeroBar (1 * q) → 0 ≤ W.ord f)
    (v : Place k ↥(modularFunctionFieldC k 1)) :
    0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩) := by sorry
