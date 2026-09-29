-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeff_mem_of_mem_integersFst_of_forall_ord_neg
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeff_mem_of_mem_integersFst_of_forall_ord_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/5efdca8a-65f1-5bf8-bae1-91c07fb6e25b
-- title:
--   A-integrality of q-expansion coefficients of R₁-integral functions
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$ (realised as `AlgebraicClosure ℚ`), a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the $q$-expansion pair) together with the Kronecker congruence `hKr` asserting $\Phi \bmod q = (C X^q - X)(C X - X^q)$, and the hypotheses $h\alpha$, $h\beta$ that the two Hecke maps `heckeAlphaBar`, `heckeBetaBar` at level $1$ and prime $q$ are integral ring homomorphisms. Let $P$ be a place specialisation for these data and let $R$ be a level-one prolongation pair for $P$, so in particular $R$ carries two regular prolongations $R_1, R_2$ of $A$ to the field $\overline{\mathbb Q}\cdot F_{\mathrm{full}}(q)$ = `modularFunctionFieldBar (1 * q)`, a subfield of the Laurent series field over $\overline{\mathbb Q}$, with residue field `modularFunctionFieldFullC (ResidueField A) 1`. Let $f$ be an element of `modularFunctionFieldBar (1 * q)` such that for every place $W$ of this field over $\overline{\mathbb Q}$ with $\operatorname{ord}_W f < 0$ one also has $\operatorname{ord}_W j < 0$, where $j$ denotes the coefficientwise image of the Laurent series `jq`; assume moreover that $f$ lies in the valuation subring $R_1.\mathrm{integers}$. Then for every $n \in \mathbb Z$ the $n$-th Laurent coefficient of $f$ lies in $A$.
--
--   This is a $q$-expansion principle in Gauss-valuation form: a function on $X_0(q)$ whose poles occur only at poles of $j$ and which is integral for the first prolongation $R_1$ has all its $q$-expansion coefficients at $\bar\infty$ in $A$. It is the variant allowing poles at both cusps, and it is used in [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.padicValRat_coeff_frickeInvolutionFull_nonneg`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.padicValRat_coeff_frickeInvolutionFull_nonneg) to control the coefficients of Fricke transforms $w_q f$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeff_mem_of_mem_integersFst_of_forall_ord_neg.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeff_mem_of_mem_integersFst_of_forall_ord_neg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (hf : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f < 0 →
      W.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : ↥(modularFunctionFieldBar (1 * q))) < 0)
    (h₁ : f ∈ R.R₁.integers) (n : ℤ) :
    (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A := by sorry
