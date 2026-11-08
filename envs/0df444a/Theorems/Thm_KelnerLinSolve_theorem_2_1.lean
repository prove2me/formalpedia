-- Prove2me | Theorems.Thm_KelnerLinSolve_theorem_2_1
-- name    : KelnerLinSolve.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:55:22.201642+00:00
-- url     : https://prove2.me/theorems/b60b230a-3104-4e95-85f1-a2f98f3599b3
-- title:
--   Theorem 2.1 — unique bounded rational vector congruent to $v$ modulo $R^L$
-- statement:
--   Let $M \in \mathbb Z^{n\times n}$ be invertible, $b\in\mathbb Z^n$, and let $R\ge2$, $L\ge1$ be integers with $\gcd(R,\det M) = 1$. Suppose $|M_{ij}|\le T$ and $|b_i|\le T$ for all $i,j$, for some $T\ge1$, and let $H$ be an integer with $H\ge n^{n/2}T^n$. Suppose $v\in\mathbb Z^n$ satisfies $Mv\equiv b\pmod{R^L}$ and
--
--   $$
--   R^L > 2H^2. \tag{4}
--   $$
--
--   Then $x^* = M^{-1}b$ is the unique vector $y \in \mathbb Q^n$ such that, writing $y_i = a_i/d_i$ in lowest terms, for every $i$
--
--   $$
--   y_i \equiv v_i \pmod{R^L}, \qquad |a_i|\le H, \qquad 1\le d_i\le H ,
--   $$
--
--   where congruence of a rational modulo $R^L$ requires its reduced denominator to be coprime to $R^L$. Both halves are asserted: $x^*$ satisfies the conditions, and every vector satisfying them equals $x^*$.
--
--   This is the uniqueness criterion that lets Dixon's $R$-adic approximation determine the exact rational solution.
--
--   Differences from the source:
--   - reading: M ∈ Z^{n×n} invertible → det M ≠ 0 (invertible over ℚ), x* = M⁻¹b computed over ℚ; reason: x* is a rational vector, so invertibility over ℚ is meant
--   - reading: T ≥ 1 (type unstated) → T a real number ≥ 1; reason: the page does not say T is an integer; the real reading is the stronger one
--   - encoding: integers R, L, H → natural numbers; reason: the hypotheses force them positive
--   - encoding: fractions a_i/d_i in lowest terms → Lean `ℚ` (`num`, `den ≥ 1`); reason: Lean stores rationals reduced
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), Theorem 2.1, p.5 (proof pp.5–6)

import Mathlib
import Definitions.Def_KelnerLinSolve_RatCongr

open Matrix

namespace KelnerLinSolve

/-- **Theorem 2.1**, Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations*, STOC 2027
submission (sha256 d1af55cb…), p.5 (proof pp.5–6). "Let `M ∈ ℤ^{n×n}` be invertible, let `b ∈ ℤⁿ`, and
let `R ≥ 2` and `L ≥ 1` be integers such that `gcd(R, det M) = 1`. Suppose `M` and `b` satisfy
entry-wise bounds `|M_{ij}| ≤ T, |bᵢ| ≤ T` for some `T ≥ 1` and for all `i` and `j`, and let `H` be an
integer with `H ≥ n^{n/2}Tⁿ`. Suppose that `v ∈ ℤⁿ` satisfies `M v ≡ b (mod R^L)`, and that
`R^L > 2H²`. (4) Then `x* = M⁻¹b` is the unique vector in `ℚⁿ` congruent to `v` modulo `R^L` such
that, when its coordinates are written as fractions `aᵢ/dᵢ` in lowest terms, `|aᵢ| ≤ H`,
`1 ≤ dᵢ ≤ H` for all `i`, where congruence of a rational number modulo `R^L` is defined only when its
reduced denominator is coprime to `R^L`."

Both halves: `x*` meets the conditions, and every vector that meets them equals `x*`.

**Formalization Note.** "Invertible" is `det M ≠ 0` (invertible over `ℚ`); `x* = M⁻¹b` is computed
over `ℚ`. `R, L, H` are naturals (the hypotheses force them positive). `T` is real.
`n^{n/2}` is `Real.rpow`. A Lean `ℚ` is in lowest terms with `den ≥ 1`. -/
theorem theorem_2_1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (R L H : ℕ) (T : ℝ)
    (v : Fin n → ℤ) (hM : M.det ≠ 0) (hR : 2 ≤ R) (hL : 1 ≤ L) (hgcd : Int.gcd (R : ℤ) M.det = 1)
    (hT : 1 ≤ T) (hMT : ∀ i j, |(M i j : ℝ)| ≤ T) (hbT : ∀ i, |(b i : ℝ)| ≤ T)
    (hH : (n : ℝ) ^ ((n : ℝ) / 2) * T ^ n ≤ H)
    (hv : ∀ i, ((R : ℤ) ^ L) ∣ (M *ᵥ v) i - b i) (h4 : 2 * H ^ 2 < R ^ L) :
    let xstar : Fin n → ℚ := (M.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ fun i => (b i : ℚ)
    let P : (Fin n → ℚ) → Prop := fun y =>
      ∀ i, RatCongr (y i) (v i) (R ^ L) ∧ |(y i).num| ≤ H ∧ (y i).den ≤ H
    P xstar ∧ ∀ y : Fin n → ℚ, P y → y = xstar := by sorry

end KelnerLinSolve
