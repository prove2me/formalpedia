-- Prove2me | Theorems.Thm_KelnerLinSolve_trials_4_4
-- name    : KelnerLinSolve.trials_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:56:34.243694+00:00
-- url     : https://prove2.me/theorems/ee420e1f-1c3b-4dd0-ab63-030cec9ed94c
-- title:
--   §4.4 — the precision search: a trial passes at $h\ge h_0+\lceil\log_2\kappa_2\rceil$; $O(\rho)$ precision, $O(\log(\rho+1))$ trials
-- statement:
--   Let $n\ge1$, $E\ge1$, $\varepsilon = 2^{-E}$, $\ell=\lceil\log_2n\rceil$, $h_0 = 6+3\ell+E$, and let the $j$-th trial use $h_j = 2^jh_0$.
--
--   1. For a normalized system $A_0,b_0$ (the hypotheses of Lemma 3.4) with $A_0$ nonsingular and any rounding to nearest, every $h\ge h_0+\lceil\log_2\kappa_2(A_0)\rceil$ gives $S = 2^h\ge64\kappa_2(A_0)n^3/\varepsilon$, and the trial at precision $h$ passes the test (8).
--   2. There is an absolute constant $C$ such that for every nonsingular $A$, with $\rho = 1+E+\lceil\log_2\kappa_2(A)\rceil+\lceil\log_2(n+1)\rceil$, every trial index $j$ that can be reached (all earlier trials had $h_i<h_0+\lceil\log_2\kappa_2(A)\rceil$) satisfies
--
--   $$
--   h_j\le C\rho,\qquad \sum_{i\le j}h_i\le C\rho,\qquad j+1\le C\log_2(\rho+1).
--   $$
--
--   Hence the largest tested $h$ and the sum of all tested $h$ are $O(\rho)$, and there are $O(\log(\rho+1))$ trials. The condition number enters only the analysis, not the algorithm.
--
--   Differences from the source:
--   - generalization: the normalized system of §4.1 (max entry < 1, ‖b₀‖_∞ < 1) → any A₀, b₀ satisfying Lemma 3.4's bounds (≤ 1); reason: §4.1's system satisfies them, so this specializes
--   - encoding: κ₂(A) in the passing threshold → κ₂(A₀) of the normalized matrix; reason: κ₂(A₀) = κ₂(A) by (9)
--   - encoding: the tested trials → every index j whose earlier trials were all below the passing threshold; reason: every tested trial is such an index
--   - encoding: O(ρ), O(log(ρ + 1)) → one absolute constant C; reason: definition of O
--   - encoding: n ≥ 1 (implicit) → hypothesis 1 ≤ n; reason: excludes the empty system, where κ₂ is meaningless
-- source:
--   Kelner, Solving Linear Systems in Õ(mn log(κ/ε)) Bit Operations, STOC 2027 submission (sha256 d1af55cb…), §4.4, p.14; h₀ from §4.2, p.13; doubling from §4.3, pp.13–14

import Mathlib
import Definitions.Def_KelnerLinSolve_kappa2
import Definitions.Def_KelnerLinSolve_trialY

namespace KelnerLinSolve

/-- **§4.4, analysis of the precision search**, Kelner, *Solving Linear Systems in Õ(mn log(κ/ε)) Bit
Operations*, STOC 2027 submission (sha256 d1af55cb…), p.14. "A trial must pass once
`h ≥ h₀ + ⌈log₂ κ₂(A)⌉`, since this ensures `S ≥ 64κ₂(A)n³/ε`. The largest tested `h` is therefore
`O(ρ)`, the sum of all tested `h` is `O(ρ)`, and there are `O(log(ρ + 1))` trials." Here
`ℓ = ⌈log₂ n⌉`, `h₀ = 6 + 3ℓ + E` (§4.2, p.13), `ε = 2^{−E}`, and the `j`-th trial uses
`h_j = 2^j h₀` (§4.3, pp.13–14: start at `h = h₀`, replace `h` by `2h`).

Two conjuncts. (a) For a normalized system `A₀, b₀` (the hypotheses of Lemma 3.4, `A₀`
nonsingular) and every `h ≥ h₀ + ⌈log₂ κ₂(A₀)⌉`: `S = 2^h ≥ 64κ₂(A₀)n³/ε`, and the trial at precision
`h` passes the test (8). (b) There is one absolute constant `C` such that, for every nonsingular `A`
with `n ≥ 1` and `E ≥ 1`, every trial index `j` that can be reached (every earlier trial `i < j` had
`h_i < h₀ + ⌈log₂ κ₂(A)⌉`) has `h_j ≤ Cρ`, `∑_{i ≤ j} h_i ≤ Cρ`, and `j + 1 ≤ C log₂(ρ + 1)`.

**Formalization Note.** The trials run on the normalized `A₀`, and `κ₂(A₀) = κ₂(A)` (§4.1, (9)
milestone); (a) is stated for `A₀` with its own `κ₂`. A trial index is "reached" only if every earlier
index was below the passing threshold of (a), which is how every tested trial is covered. -/
theorem trials_4_4 :
    (∀ {n : ℕ} (E h : ℕ) (A₀ : Matrix (Fin n) (Fin n) ℝ) (b₀ : Fin n → ℝ) (rnd : ℝ → ℤ),
      1 ≤ n → 1 ≤ E → (1 / 2 ≤ maxAbsEntry A₀ ∧ maxAbsEntry A₀ ≤ 1) →
      (1 / 2 ≤ infNorm b₀ ∧ infNorm b₀ ≤ 1) → A₀.det ≠ 0 → IsNearestRounding rnd →
      6 + 3 * Nat.clog 2 n + E + ⌈Real.logb 2 (kappa2 A₀)⌉₊ ≤ h →
        64 * kappa2 A₀ * (n : ℝ) ^ 3 / (2 : ℝ) ^ (-(E : ℤ)) ≤ (2 : ℝ) ^ h ∧
        8 * (n : ℝ) ^ 2 * (infNorm (trialY rnd A₀ b₀ h) + 1) ≤ (2 : ℝ) ^ (-(E : ℤ)) * (2 : ℝ) ^ h) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (E : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), 1 ≤ n → 1 ≤ E → A.det ≠ 0 →
      ∀ j : ℕ, (∀ i < j, 2 ^ i * (6 + 3 * Nat.clog 2 n + E) <
          6 + 3 * Nat.clog 2 n + E + ⌈Real.logb 2 (kappa2 A)⌉₊) →
        ((2 ^ j * (6 + 3 * Nat.clog 2 n + E) : ℕ) : ℝ) ≤ C * rho n E (kappa2 A) ∧
        ((∑ i ∈ Finset.range (j + 1), 2 ^ i * (6 + 3 * Nat.clog 2 n + E) : ℕ) : ℝ)
          ≤ C * rho n E (kappa2 A) ∧
        ((j + 1 : ℕ) : ℝ) ≤ C * Real.logb 2 (rho n E (kappa2 A) + 1)) := by sorry

end KelnerLinSolve
