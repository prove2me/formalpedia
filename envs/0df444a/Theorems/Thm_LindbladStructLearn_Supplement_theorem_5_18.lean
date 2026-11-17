-- Prove2me | Theorems.Thm_LindbladStructLearn_Supplement_theorem_5_18
-- name    : LindbladStructLearn.Supplement.theorem_5_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:47:05.928407+00:00
-- url     : https://prove2.me/theorems/9986e520-4996-40f7-94c1-d2e2f5d45392
-- title:
--   Theorem 5.18 — structure learning Hamiltonians from high-temperature Gibbs states with $O(\log(n/\delta)/(\beta\varepsilon)^2)$ copies
-- statement:
--   Let $k\ge1$. There are a constant $C>0$ and an exponent $a$, both depending only on $k$, and a single algorithm with the following guarantee. Let $n\ge1$, $d\ge0$, $\varepsilon>0$, $\delta\in(0,1)$, and let $\beta$ satisfy
--   $$0<\beta\le\frac{1}{1000\,e^6(2kd+1)^8}.$$
--   Let $H=i\sum_P\lambda_PP$ be a $k$-local Hamiltonian on $n$ qubits with purely imaginary coefficients and $\|\lambda\|_\infty\le1$, in which every qubit interacts with at most $d$ nonzero terms. Given $n,d,\beta,\varepsilon,\delta$ and copies of the Gibbs state $\rho_\beta=e^{-\beta H}/\operatorname{tr}(e^{-\beta H})$, each measured in a Pauli basis, the algorithm outputs $\widehat\lambda$ with
--   $$\|\widehat\lambda-\lambda\|_\infty\le\varepsilon\qquad\text{with probability at least }1-\delta.$$
--   It uses at most $C\log(2n/\delta)/(\beta\varepsilon)^2$ copies. Its classical runtime is at most $C\big(1+n^k(1+d)^a\log(2n/\delta)/(\beta\varepsilon)^2\big)$ on every run.
--
--   This is the first structure-learning algorithm for Hamiltonians from Gibbs states (informally Theorem 1.8).
--
--   **Formalization Note** The algorithm is one admissible program of the published learner's machine. Its experiment instruction applies the replacement channel $\rho\mapsto\operatorname{tr}(\rho)\rho_\beta$ and then measures in a Pauli basis. Each experiment therefore consumes one copy, and the copies are counted as experiments. $\widehat\lambda_P$ is the decoded output on the pair $(P,I)$, and $\mathrm{poly}(d)$ is $(1+d)^a$.
--
--   Differences from the source:
--   - generalization: an algorithm using copies of the Gibbs state ρ_β (any measurement) → one admissible program of the published learner machine whose experiments measure fresh copies of ρ_β in Pauli bases; reason: a restricted existential implies the printed one; the proof estimates E_P(λ) by classical shadows [HKP20], which use random Pauli-basis measurements
--   - encoding: every qubit interacts with at most d nonzero terms → deg(hamVec λ) ≤ d (the published degree of the embedded coefficient vector); reason: the published deg counts, per qubit, the nonzero terms acting on it
--   - encoding: O(log(n/δ)/(βε)²) copies; runtime O(n^k poly(d) log(n/δ)/(βε)²), k = O(1) → copies ≤ C log(2n/δ)/(βε)² on every reachable configuration; all runs halted within N = ⌈C(1 + n^k(1+d)^a log(2n/δ)/(βε)²)⌉ steps with work at most N; C, a depending only on k; reason: O(·) and poly(d) as explicit k-dependent constants; log(2n/δ) keeps the logarithm positive at n = 1, and the additive constant covers reading the input
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 5.18, p.52 (informal Theorem 1.8, p.5); proof p.53

import Mathlib
import Definitions.Def_LindbladStructLearn_Supplement_HamiltonianModel
import Definitions.Def_LindbladStructLearn_Supplement_Session
import Definitions.Def_LindbladStructLearn_Admissible
import Definitions.Def_LindbladStructLearn_mass
import Definitions.Def_LindbladStructLearn_deg

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal

namespace LindbladStructLearn.Supplement

open LindbladTolerant.Testing LindbladStructLearn

/-- Theorem 5.18 (structure learning of Hamiltonians from high-temperature Gibbs states;
Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version,
sha256 0af12079…2eb52e), p.52; informal Theorem 1.8, p.5). Let `ε, δ > 0` and `k = O(1)`. Let
`H = i Σ_P λ_P P` be a `k`-local Hamiltonian with `‖λ‖_∞ ≤ 1` in which every qubit interacts with at
most `d` nonzero terms, and let `0 < β ≤ 1/(1000 e⁶ (2kd + 1)⁸)`. There is an algorithm that finds `λ̂`
with `‖λ̂ − λ‖_∞ ≤ ε` with probability at least `1 − δ` using `O(log(n/δ)/(βε)²)` copies of
`ρ_β = e^(−βH)/tr(e^(−βH))`; its classical runtime is `O(n^k poly(d) log(n/δ)/(βε)²)`.

**Formalization Note**
1. The algorithm is one admissible program of the published learner's machine, chosen after `k` and
   before `n, d, β, ε, δ, λ`. Its only access to `H` is the `experiment` instruction with the
   replacement channel `ρ ↦ tr(ρ) ρ_β` (`gibbsChannel`): each experiment measures a fresh copy of
   `ρ_β` in a Pauli basis, and the number of copies is the number of experiments
   (`durations.length`). Input: `n, d` (integer cells 0, 1), `β, ε, δ` (real cells 0, 1, 2). Output:
   `λ̂_P` is the decoded value of the pair `(P, I)`.
2. Constants depend only on `k`; `poly(d)` is `(1 + d)^a` with `a` depending only on `k`;
   `log(n/δ)` is `log(2n/δ)`; the runtime carries an additive constant and holds on every run (all
   runs halted within `N` steps, work at most `N`). The copy bound holds on every reachable
   configuration. -/
theorem theorem_5_18 (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ P : Program, Admissible P ∧
      ∀ n : ℕ, 1 ≤ n → ∀ d : ℕ, ∀ β : ℝ, 0 < β →
      β ≤ 1 / (1000 * Real.exp 6 * (2 * k * d + 1) ^ 8) →
      ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ lam : HIdx n k → ℂ, (∀ P, (lam P).re = 0) → (∀ P, ‖lam P‖ ≤ 1) → deg (hamVec lam) ≤ d →
        let evo : ℝ → Super (Qubits n) (Qubits n) := fun _ => gibbsChannel β lam
        let s₀ : MState := listInput [(n : ℤ), (d : ℤ)] [β, ε, δ]
        let N : ℕ := ⌈C * (1 + (n : ℝ) ^ k * (1 + d : ℝ) ^ a * Real.log (2 * n / δ) / (β * ε) ^ 2)⌉₊
        (∀ s, Reach P n evo N s₀ s → Halted s ∧ s.work ≤ N) ∧
        1 - ENNReal.ofReal δ ≤ mass P n evo N s₀ (fun s => Halted s ∧
          ∀ Q : HIdx n k, ‖decode n k s (Q.1, 0) - lam Q‖ ≤ ε) ∧
        ∀ (M : ℕ) (s : MState), Reach P n evo M s₀ s →
          (s.durations.length : ℝ) ≤ C * Real.log (2 * n / δ) / (β * ε) ^ 2 := by sorry

end LindbladStructLearn.Supplement
