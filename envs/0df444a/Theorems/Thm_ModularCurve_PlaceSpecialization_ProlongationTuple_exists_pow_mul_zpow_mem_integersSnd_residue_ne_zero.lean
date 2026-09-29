-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/92fc4524-f108-5361-9468-9feded00d9f8
-- title:
--   Correcting an exponent by powers of a non-unit
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Fix furthermore data $data$ consisting of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ with $\Phi(j(q\tau), j(\tau)) = 0$, a proof $hKr$ that the reduction of $\Phi$ modulo $q$ in both variables equals $(C(X)^q - X)(C(X) - X^q)$, and proofs $h\alpha$, $h\beta$ that the two degeneracy embeddings $\overline{\mathbb{Q}}$-base-changed from level $N$ to level $Nq$ are integral ring homomorphisms. Let $P$ be a place specialisation of these data and $R$ a prolongation tuple over $P$; in particular $R$ provides a regular prolongation $R_2$, that is a valuation subring `R.R₂.integers` of the level-$Nq$ function field $\overline{\mathbb{Q}}$-base-changed inside Laurent series, together with a surjective residue homomorphism onto the level-$N$ function field over the residue field of $A$, whose kernel is the maximal ideal and which is compatible with $A \to \mathrm{ResidueField}(A)$ on constants. Let $u \neq 0$ in the level-$Nq$ function field be such that whenever $u$ lies in `R.R₂.integers` its residue vanishes, and let $f \neq 0$. Then there exist $m \in \mathbb{N}$ with $m \neq 0$ and $j \in \mathbb{Z}$ such that $f^m u^j$ lies in `R.R₂.integers` and has nonzero residue.
--
--   This is the exponent-correction step for the second of the two valuation rings attached to a prolongation tuple: a nonzero function can be made integral with nonzero residue after passing to a suitable power and multiplying by an integral power of a fixed non-unit, the underlying point being the commensurability of the value groups involved. It is used in the one-sided forms of the divisor laws for the first and second prolongation and in the one-sided cusp law at infinity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_pow_mul_zpow_mem_integersSnd_residue_ne_zero
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (u : modularFunctionFieldBar (N * q)) (hu0 : u ≠ 0)
    (hu : ∀ h₂ : u ∈ R.R₂.integers, R.R₂.residue ⟨u, h₂⟩ = 0)
    (f : modularFunctionFieldBar (N * q)) (hf : f ≠ 0) :
    ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
      ∃ h₂ : f ^ m * u ^ j ∈ R.R₂.integers, R.R₂.residue ⟨f ^ m * u ^ j, h₂⟩ ≠ 0 := by sorry
