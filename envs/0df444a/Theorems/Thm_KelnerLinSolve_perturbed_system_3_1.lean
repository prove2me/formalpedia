-- Prove2me | Theorems.Thm_KelnerLinSolve_perturbed_system_3_1
-- name    : KelnerLinSolve.perturbed_system_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:12.708201+00:00
-- url     : https://prove2.me/theorems/8b5bb48f-4425-4d56-9969-7dab97a4bc16
-- title:
--   §3.1 — parameters for $M = RA+I$, the simplified recurrence, and exact recovery of $(I+RA)^{-1}b$
-- statement:
--   Let $n\ge1$, $A\in\mathbb Z^{n\times n}$, $b\in\mathbb Z^n$, $T_A = \max\{1,\max_{i,j}|A_{ij}|,\max_i|b_i|\}$, and let $R = 2^s\ge 2nT_A$ with $s\ge1$. Put $M = RA+I$, $T_M = \max(\max_{i,j}|M_{ij}|,\max_i|b_i|)$, $H = R^{3n}$ and $L = 6n+2$. No assumption is made on $A$ beyond this. Then:
--
--   1. $\det M\equiv1\pmod R$, $M$ is nonsingular, and $\gcd(R,\det M)=1$;
--   2. $n\le R$ and $T_M\le RT_A+1\le R^2/(2n)+1\le R^2$;
--   3. $n^{n/2}T_M^n\le R^{n/2}R^{2n}=R^{5n/2}\le R^{3n}$;
--   4. $2H^2 = 2R^{6n}$ and $R^L = R^{6n+2}\ge4R^{6n}>2H^2$;
--   5. Dixon's recurrence with $C = I$ is Lines 3–4 of Algorithm 1: $x_i = b_i\bmod R$ and $b_{i+1} = (b_i-x_i)/R - Ax_i$;
--   6. the assembled vector $y_L = \sum_{i<L}R^ix_i$ has entries in $\{0,\dots,R^L-1\}$, and $(I+RA)^{-1}b$ is the unique rational vector congruent to $y_L$ modulo $R^L$ whose reduced numerators and denominators are at most $H$.
--
--   Item 6 is the correctness part of the proof of Theorem 3.3 (p.10), obtained from items 1–5 and Theorem 2.1.
--
--   Differences from the source:
--   - encoding: n^{n/2}, R^{n/2}, R^{5n/2} → `Real.rpow`; reason: same values
--   - encoding: (I + RA)⁻¹ b → inverse over ℚ; reason: M is nonsingular, so this is the true inverse
--   - encoding: n ≥ 1 (implicit; the page divides by 2n) → hypothesis 1 ≤ n; reason: excludes the empty system, where the chain T_M ≤ RT_A + 1 ≤ R²/(2n) + 1 has no meaning
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §3.1, p.9; Algorithm 1, p.9; proof of Theorem 3.3, p.10

import Mathlib
import Definitions.Def_KelnerLinSolve_RatCongr
import Definitions.Def_KelnerLinSolve_dixonRes
import Definitions.Def_KelnerLinSolve_solvePerturbedRes

open Matrix

namespace KelnerLinSolve

/-- **§3.1, the parameters of Dixon's algorithm for `M = RA + I` and the simplified recurrence**,
Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027 submission
(sha256 d1af55cb…), p.9, with the correctness argument of Theorem 3.3's proof, p.10. "Let
`M = RA + I` with `R = 2^s ≥ 2nT_A` and `s ≥ 1`. Since `det(M) ≡ 1 (mod R)`, `M` is nonsingular and
`gcd(R, det(M)) = 1` … Let `T_M = max(max_{i,j} |M_{ij}|, maxᵢ |bᵢ|) ≤ RT_A + 1` … `n ≤ R` and
`T_M ≤ RT_A + 1 ≤ R²/(2n) + 1 ≤ R²`, so `n^{n/2}T_Mⁿ ≤ R^{n/2}R^{2n} = R^{5n/2} ≤ R^{3n}`, and thus
`H = R^{3n}` is an admissible height bound, with `2H² = 2R^{6n}`. If we choose `L = 6n + 2`, we'll
then have `R^L = R^{6n+2} ≥ 4R^{6n} > 2H²` … Equation (2) becomes `xᵢ := bᵢ mod R`, and plugging
`M = RA + I` into (3) gives `b_{i+1} := (bᵢ − xᵢ)/R − Axᵢ`."

For `A ∈ ℤ^{n×n}`, `b ∈ ℤⁿ`, `n ≥ 1`, `s ≥ 1` and `R = 2^s ≥ 2nT_A`, with no assumption on `A`
beyond this: (1) `det M ≡ 1 (mod R)`; (2) `M` nonsingular; (3) `gcd(R, det M) = 1`; (4) the chain
for `T_M`; (5) the chain for `n^{n/2}T_Mⁿ`; (6) the chain for `R^L`; (7) Dixon's recurrence with
`C = I` is Lines 3–4 of Algorithm 1; (8) the assembled `y_L` has entries in `{0, …, R^L − 1}`
and `(I + RA)⁻¹b` is the unique rational vector congruent to `y_L` modulo `R^L` with reduced
numerators and denominators at most `H`.

**Formalization Note.** `T_A` is `heightTA A b`; the inverse `(I + RA)⁻¹` is taken over `ℚ`.
`R^{n/2}`, `R^{5n/2}` and `n^{n/2}` are `Real.rpow`. -/
theorem perturbed_system_3_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (s : ℕ)
    (hn : 1 ≤ n) (hs : 1 ≤ s) (hR : 2 * n * heightTA A b ≤ 2 ^ s) :
    let R : ℕ := 2 ^ s
    let M : Matrix (Fin n) (Fin n) ℤ := (R : ℤ) • A + 1
    let TM : ℕ := max (Finset.univ.sup fun p : Fin n × Fin n => (M p.1 p.2).natAbs)
      (Finset.univ.sup fun i => (b i).natAbs)
    let H : ℕ := R ^ (3 * n)
    let L : ℕ := 6 * n + 2
    let y : Fin n → ℤ := dixonPrefix M 1 (R : ℤ) b L
    let z : Fin n → ℚ := (M.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ fun i => (b i : ℚ)
    let P : (Fin n → ℚ) → Prop := fun w =>
      ∀ i, RatCongr (w i) (y i) (R ^ L) ∧ |(w i).num| ≤ H ∧ (w i).den ≤ H
    ((R : ℤ) ∣ M.det - 1) ∧
    M.det ≠ 0 ∧
    Int.gcd (R : ℤ) M.det = 1 ∧
    (n ≤ R ∧ (TM : ℝ) ≤ R * heightTA A b + 1 ∧
      (R : ℝ) * heightTA A b + 1 ≤ (R : ℝ) ^ 2 / (2 * n) + 1 ∧ (R : ℝ) ^ 2 / (2 * n) + 1 ≤ (R : ℝ) ^ 2) ∧
    ((n : ℝ) ^ ((n : ℝ) / 2) * (TM : ℝ) ^ n ≤ (R : ℝ) ^ ((n : ℝ) / 2) * (R : ℝ) ^ (2 * n) ∧
      (R : ℝ) ^ ((n : ℝ) / 2) * (R : ℝ) ^ (2 * n) = (R : ℝ) ^ ((5 * n : ℝ) / 2) ∧
      (R : ℝ) ^ ((5 * n : ℝ) / 2) ≤ (R : ℝ) ^ (3 * n)) ∧
    (2 * H ^ 2 = 2 * R ^ (6 * n) ∧ 4 * R ^ (6 * n) ≤ R ^ L ∧ 2 * H ^ 2 < 4 * R ^ (6 * n)) ∧
    (∀ i : ℕ, dixonRes M 1 (R : ℤ) b i = solvePerturbedRes A (R : ℤ) b i ∧
      dixonDigit M 1 (R : ℤ) b i = fun r => solvePerturbedRes A (R : ℤ) b i r % (R : ℤ)) ∧
    ((∀ r, 0 ≤ y r ∧ y r < (R : ℤ) ^ L) ∧ P z ∧ ∀ w : Fin n → ℚ, P w → w = z) := by sorry

end KelnerLinSolve
