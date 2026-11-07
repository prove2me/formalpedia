-- Prove2me | Theorems.Thm_IterRoundDet_theorem_4_1
-- name    : IterRoundDet.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:38.70989+00:00
-- url     : https://prove2.me/theorems/0ce3f30d-a8d4-4de9-a9af-f5f6cde6c5a6
-- title:
--   Theorem 4.1 — rounding a rational $(a_0,x_0)\in\mathcal R$ to a base with $\log p(\mathbf 1_B)\ge f(a_0,x_0)-14d-\varepsilon$
-- statement:
--   Given an initial feasible point $(a_0,x_0)\in\mathcal R$ and an accuracy parameter $\varepsilon>0$, there is an algorithm that returns a basis $B\in\mathcal B(\mathcal M)$ with
--
--   $$\log p(\mathbf 1_B)\ge f(a_0,x_0)-14d-\varepsilon.$$
--
--   The running time is polynomial in $n$, $b$ and $1/\varepsilon$. The algorithm is deterministic given a value oracle for $p$, and succeeds with probability at least $1-\rho$ (for any $\rho\in(0,1)$, in time $\mathrm{poly}(\log(1/\rho))$) given a coefficient oracle. This is the rounding half of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
--   - reading: a polynomial-time algorithm, no machine named → one finite program on a log-cost oracle RAM, with C and K before the instance; time C(2+n+b+N)^K; reason: the paper counts bits (pp.19, 21, 41); every reasonable bit model gives the same class
--   - encoding: independence, value and coefficient oracles → tagged query instructions, rationals as (zigzag numerator, denominator), sets as characteristic words, ill-formed queries answered by zeros; reason: a syntactic program needs a concrete layout; no instance changes
--   - reading: for any ε > 0 (and ρ ∈ (0,1)), an algorithm → one program for all real ε, ρ, reading N = ⌈1/ε⌉₊ and L = ⌈log₂(1/ρ)⌉₊ from the input; reason: uniform in ε and ρ, which is what polynomial in 1/ε and log(1/ρ) on p.19 says; it implies the fixed-ε form
--   - reading: a value oracle for p, with b the maximum bit length of the coefficients → the value clause also assumes AnswerBits b c: the answer p(z) has at most 2b + n + 2∑(bits of z_i) bits; reason: a bit-counting algorithm must read the answers, so the page presupposes polynomial-length answers; a common denominator of b bits implies this (integer coefficients, rational determinants), proved in the sanity file
--   - reading: succeeds with probability at least 1 − ρ, in polynomial time → time on every coin tape; success counted over tapes as (1 − ρ)2^T ≤ #{good tapes}; reason: the proofs cap every loop and report failure as an outcome (p.40); a time bound on every tape is the stronger form
--   - reading: time polynomial in n, b, 1/ε → time also polynomial in L₀, the bit length of the encoding of (a₀, x₀), which is rational; reason: a machine cannot read an arbitrarily long input; Lemma C.4 counts "the state encoding length", and Proposition C.5 outputs a point of polynomial length, so the composition is unaffected
--   - encoding: log p(1_B) ≥ f(a₀, x₀) − 14d − ε, with log 0 = −∞ → exp(f(a₀, x₀) − 14d − ε) ≤ p(1_B); reason: the same statement, and it forces p(1_B) > 0, as the printed line does
--   - encoding: a matroid M on [n] of rank r ≥ d → M : Matroid (Fin n), M.E = univ, (d : ℕ∞) ≤ M.eRank; reason: Mathlib form; r is not an input, as the greedy algorithm computes it
--   - encoding: returns a base B → out = some (setCode B) with M.IsBase B; reason: the output of a machine is a list of cells
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Theorem 4.1, p.19

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation
import Definitions.Def_IterRoundDet_Machine
import Definitions.Def_IterRoundDet_Oracles

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Theorem 4.1, p.19. Given an initial feasible point `(a₀, x₀) ∈ R` and an accuracy parameter `ε > 0`, there
is an algorithm that returns a basis `B ∈ B(M)` with `log p(1_B) ≥ f(a₀, x₀) − 14d − ε`. The running time is polynomial in
`n, b, 1/ε`. The algorithm is deterministic given a value oracle for `p`, and succeeds with probability at least `1 − ρ`
(for any `ρ ∈ (0, 1)`, in time `poly(log(1/ρ))`) given a coefficient oracle.

**Formalization Note.** Two clauses, each with its program and constants before the instance. Time also counts `L₀`, the bit
length of the encoding of the rational input `(a₀, x₀)`, since a machine cannot read a long input in less time. The time bound
holds on every tape. The conclusion is the multiplicative form of the printed line. The input is
`[n, d, b, N] ++ (a₀, x₀)` with `N = ⌈1/ε⌉₊`, plus `L = ⌈log₂(1/ρ)⌉₊` in the second clause. -/
theorem theorem_4_1 :
    (∃ (P : Program) (C K : ℕ), CoinFree P ∧
      ∀ (n d b : ℕ) (c : Finset (Fin n) → ℚ) (M : Matroid (Fin n)) (ε : ℝ) (a₀ x₀ : Fin n → ℚ),
        IsStablePoly d (castCoef c) → M.E = Set.univ → (d : ℕ∞) ≤ M.eRank →
        BitBounded b c → AnswerBits b c → 0 < ε →
        Feasible (castCoef c) M (fun i => (a₀ i : ℝ)) (fun i => (x₀ i : ℝ)) →
        let N := ⌈1 / ε⌉₊
        let L₀ := listBits (ratList a₀ ++ ratList x₀)
        let T := C * (2 + n + b + N + L₀) ^ K
        let s := run P (valueModel M c) ([n, d, b, N] ++ ratList a₀ ++ ratList x₀) (fun _ => false) T
        s.out.isSome ∧ s.cost ≤ T ∧ ∃ B : Finset (Fin n), s.out = some (setCode B) ∧
          M.IsBase (B : Set (Fin n)) ∧
          Real.exp (relaxObj (castCoef c) (fun i => (a₀ i : ℝ)) (fun i => (x₀ i : ℝ)) - 14 * d - ε) ≤
            pEval (castCoef c) (ind B)) ∧
    (∃ (P : Program) (C K : ℕ),
      ∀ (n d b : ℕ) (c : Finset (Fin n) → ℚ) (M : Matroid (Fin n)) (ε ρ : ℝ) (a₀ x₀ : Fin n → ℚ),
        IsStablePoly d (castCoef c) → M.E = Set.univ → (d : ℕ∞) ≤ M.eRank →
        BitBounded b c → 0 < ε → 0 < ρ → ρ < 1 →
        Feasible (castCoef c) M (fun i => (a₀ i : ℝ)) (fun i => (x₀ i : ℝ)) →
        let N := ⌈1 / ε⌉₊
        let L := ⌈Real.logb 2 (1 / ρ)⌉₊
        let L₀ := listBits (ratList a₀ ++ ratList x₀)
        let T := C * (2 + n + b + N + L + L₀) ^ K
        let input := [n, d, b, N, L] ++ ratList a₀ ++ ratList x₀
        (∀ w : Fin T → Bool,
          (run P (coeffModel M c) input (extendBits w) T).out.isSome ∧
          (run P (coeffModel M c) input (extendBits w) T).cost ≤ T) ∧
        (1 - ρ) * (2 : ℝ) ^ T ≤ (Nat.card {w : Fin T → Bool //
          ∃ B : Finset (Fin n),
            (run P (coeffModel M c) input (extendBits w) T).out = some (setCode B) ∧
            M.IsBase (B : Set (Fin n)) ∧
            Real.exp (relaxObj (castCoef c) (fun i => (a₀ i : ℝ)) (fun i => (x₀ i : ℝ)) - 14 * d - ε) ≤
              pEval (castCoef c) (ind B)} : ℝ)) := by sorry

end IterRoundDet
