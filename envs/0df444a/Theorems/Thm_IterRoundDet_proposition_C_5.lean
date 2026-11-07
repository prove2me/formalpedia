-- Prove2me | Theorems.Thm_IterRoundDet_proposition_C_5
-- name    : IterRoundDet.proposition_C_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:45.882786+00:00
-- url     : https://prove2.me/theorems/29c300ed-b6d1-4c77-8e0b-1e1c016c8f6f
-- title:
--   Proposition C.5 — computing a rational $(a_0,x_0)\in\mathcal R$ with $f(a_0,x_0)\ge\mathrm{REL}-\varepsilon$
-- statement:
--   Suppose $\mathcal R\ne\emptyset$. For any $\varepsilon,\rho\in(0,1)$, one can compute a rational $(a_0,x_0)\in\mathcal R$ satisfying
--
--   $$f(a_0,x_0)\ge\mathrm{REL}-\varepsilon$$
--
--   in time $\mathrm{poly}(n,b,1/\varepsilon,\log(1/\rho))$, deterministically with a value oracle and with probability at least $1-\rho$ with a coefficient oracle. This is the optimization half of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
--   - reading: a polynomial-time algorithm, no machine named → one finite program on a log-cost oracle RAM, with C and K before the instance; time C(2+n+b+N)^K; reason: the paper counts bits (pp.19, 21, 41); every reasonable bit model gives the same class
--   - encoding: independence, value and coefficient oracles → tagged query instructions, rationals as (zigzag numerator, denominator), sets as characteristic words, ill-formed queries answered by zeros; reason: a syntactic program needs a concrete layout; no instance changes
--   - generalization: rational ε, ρ ∈ (0, 1) → real ε, ρ ∈ (0, 1), through N = ⌈1/ε⌉₊ and L = ⌈log₂(1/ρ)⌉₊; reason: the input is N and L, not ε and ρ; every rational pair is a special case and its bit length does not enter
--   - reading: a value oracle for p, with b the maximum bit length of the coefficients → the value clause also assumes AnswerBits b c: the answer p(z) has at most 2b + n + 2∑(bits of z_i) bits; reason: a bit-counting algorithm must read the answers, so the page presupposes polynomial-length answers; a common denominator of b bits implies this (integer coefficients, rational determinants), proved in the sanity file
--   - reading: succeeds with probability at least 1 − ρ, in polynomial time → time on every coin tape; success counted over tapes as (1 − ρ)2^T ≤ #{good tapes}; reason: the proofs cap every loop and report failure as an outcome (p.40); a time bound on every tape is the stronger form
--   - encoding: f(a₀, x₀) ≥ REL − ε → for all (a, x) ∈ R, f(a, x) − ε ≤ f(a₀, x₀); reason: REL is the maximum of f over R
--   - encoding: a matroid M on [n] of rank r ≥ d → M : Matroid (Fin n), M.E = univ, (d : ℕ∞) ≤ M.eRank; reason: Mathlib form; r is not an input, as the greedy algorithm computes it
--   - encoding: computes a rational (a₀, x₀) → out = some (ratList a₀ ++ ratList x₀); reason: the output of a machine is a list of cells
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Proposition C.5, p.40

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation
import Definitions.Def_IterRoundDet_Machine
import Definitions.Def_IterRoundDet_Oracles

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Proposition C.5 (Solving the relaxation), p.40. Suppose `R ≠ ∅`. For any rational `ε, ρ ∈ (0, 1)`, we can compute a
rational `(a₀, x₀) ∈ R` with `f(a₀, x₀) ≥ REL − ε` in time `poly(n, b, 1/ε, log(1/ρ))`, deterministically with a value oracle and
with probability at least `1 − ρ` with a coefficient oracle.

**Formalization Note.** Two clauses, each with its program and constants before the instance. `REL − ε ≤ f(a₀, x₀)` is `∀ (a′, x′) ∈ R,
f(a′, x′) − ε ≤ f(a₀, x₀)`. The parameters are real, entering through `N = ⌈1/ε⌉₊` and `L = ⌈log₂(1/ρ)⌉₊`, which covers the rational ones.
The output is `ratList a₀ ++ ratList x₀`; the time bound holds on every tape. -/
theorem proposition_C_5 :
    (∃ (P : Program) (C K : ℕ), CoinFree P ∧
      ∀ (n d b : ℕ) (c : Finset (Fin n) → ℚ) (M : Matroid (Fin n)) (ε : ℝ),
        IsStablePoly d (castCoef c) → M.E = Set.univ → (d : ℕ∞) ≤ M.eRank →
        BitBounded b c → AnswerBits b c → 0 < ε → ε < 1 →
        (∃ a x, Feasible (castCoef c) M a x) →
        let N := ⌈1 / ε⌉₊
        let T := C * (2 + n + b + N) ^ K
        let s := run P (valueModel M c) [n, d, b, N] (fun _ => false) T
        s.out.isSome ∧ s.cost ≤ T ∧ ∃ a₀ x₀ : Fin n → ℚ, s.out = some (ratList a₀ ++ ratList x₀) ∧
          Feasible (castCoef c) M (fun i => (a₀ i : ℝ)) (fun i => (x₀ i : ℝ)) ∧
          ∀ a x, Feasible (castCoef c) M a x →
            relaxObj (castCoef c) a x - ε ≤
              relaxObj (castCoef c) (fun i => (a₀ i : ℝ)) (fun i => (x₀ i : ℝ))) ∧
    (∃ (P : Program) (C K : ℕ),
      ∀ (n d b : ℕ) (c : Finset (Fin n) → ℚ) (M : Matroid (Fin n)) (ε ρ : ℝ),
        IsStablePoly d (castCoef c) → M.E = Set.univ → (d : ℕ∞) ≤ M.eRank →
        BitBounded b c → 0 < ε → ε < 1 → 0 < ρ → ρ < 1 →
        (∃ a x, Feasible (castCoef c) M a x) →
        let N := ⌈1 / ε⌉₊
        let L := ⌈Real.logb 2 (1 / ρ)⌉₊
        let T := C * (2 + n + b + N + L) ^ K
        let input := [n, d, b, N, L]
        (∀ w : Fin T → Bool,
          (run P (coeffModel M c) input (extendBits w) T).out.isSome ∧
          (run P (coeffModel M c) input (extendBits w) T).cost ≤ T) ∧
        (1 - ρ) * (2 : ℝ) ^ T ≤ (Nat.card {w : Fin T → Bool //
          ∃ a₀ x₀ : Fin n → ℚ,
            (run P (coeffModel M c) input (extendBits w) T).out = some (ratList a₀ ++ ratList x₀) ∧
            Feasible (castCoef c) M (fun i => (a₀ i : ℝ)) (fun i => (x₀ i : ℝ)) ∧
            ∀ a x, Feasible (castCoef c) M a x →
              relaxObj (castCoef c) a x - ε ≤
                relaxObj (castCoef c) (fun i => (a₀ i : ℝ)) (fun i => (x₀ i : ℝ))} : ℝ)) := by sorry

end IterRoundDet
