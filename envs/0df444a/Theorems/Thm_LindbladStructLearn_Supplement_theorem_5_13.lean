-- Prove2me | Theorems.Thm_LindbladStructLearn_Supplement_theorem_5_13
-- name    : LindbladStructLearn.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:45:42.699253+00:00
-- url     : https://prove2.me/theorems/1bed0461-3cc3-478e-babb-03589d1e8a17
-- title:
--   Theorem 5.13 — structure learning Hamiltonians from real-time evolution with $O(g\log(n/\delta)/\varepsilon^2)$ total evolution time
-- statement:
--   Let $k\ge1$. There are constants $C,c>0$ depending only on $k$ and a single algorithm with the following guarantee. Let $n\ge1$, $g>0$, $\varepsilon>0$ and $\delta\in(0,1)$. Let $H=i\sum_P\lambda_PP$ be a $k$-local Hamiltonian on $n$ qubits with purely imaginary coefficients, $\|\lambda\|_{B_1}\le g$ and $\|\lambda\|_\infty\le1$. Given $n,g,\varepsilon,\delta$ and access to $e^{-iH\tau}$ through Pauli experiments, the algorithm outputs $\widehat\lambda$ with
--   $$\|\widehat\lambda-\lambda\|_\infty\le\varepsilon\qquad\text{with probability at least }1-\delta.$$
--   Every evolution time $\tau$ it uses lies in $[c/g,\,1/(162kg))$, and its total evolution time is at most
--   $$t_{\mathrm{total}}\le C\,\frac{g\log(2n/\delta)}{\varepsilon^2}.$$
--   Its classical runtime is at most
--   $$C\Big(1+\frac{n^kg^2}{\varepsilon^2}\Big)\big(1+\log^+(1/\varepsilon)\big)\log\frac{2n}{\delta\min(\varepsilon,1)}$$
--   on every run.
--
--   This is the Hamiltonian counterpart of Theorem 1.1 (informally Theorem 1.7). The total evolution time is independent of the degree of the interaction graph.
--
--   **Formalization Note** The algorithm is one admissible program of the published learner's machine. Its only quantum operation prepares a Pauli eigenstate, evolves it under $e^{-iH\tau}$, and measures it in a Pauli basis. $\widehat\lambda_P$ is its decoded output on the pair $(P,I)$.
--
--   Differences from the source:
--   - reading: "let 0 < t < 1/(162kg)", a parameter that does not occur in the conclusion → the algorithm chooses its evolution times: every duration τ satisfies c/g ≤ τ < 1/(162kg), with c depending only on k; reason: read as an input that the algorithm must use for every such t, the bound O(g log(n/δ)/ε²) is false as t → 0 (n = 1, H = λZ: an experiment of duration t changes outcome laws by O(εt) between λ = 0 and λ = 2ε, so ~1/(tε)² experiments and total time ~1/(tε²) are needed); the time resolution Θ(1/g) is that of the informal Theorem 1.7
--   - generalization: there exists an algorithm → there is one admissible program of the published Pauli-experiment machine, chosen per k before n, g, ε, δ, λ; reason: a restricted existential implies the printed one; the proof uses Algorithm 1 (Pauli eigenstates and Pauli-basis measurements, Lemma 2.10)
--   - encoding: t_total = O(g log(n/δ)/ε²); runtime O((n^k g²/ε²) log(1/ε) log(n/(δε))) → C·g·log(2n/δ)/ε² on every reachable configuration; runtime: all runs halted within N = ⌈C(1 + n^k g²/ε²)(1 + log⁺(1/ε)) log(2n/(δ min(ε,1)))⌉ steps with work at most N; reason: O(·) as explicit constants depending only on k (the proof's C^k); the factors 2, 1 + and min(ε,1) keep each logarithm positive at n = 1, ε ≥ 1, δ → 1, and the additive constant covers reading the input
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 5.13, p.48 (informal Theorem 1.7, p.5); proof pp.48–52

import Mathlib
import Definitions.Def_LindbladStructLearn_Supplement_HamiltonianModel
import Definitions.Def_LindbladStructLearn_Supplement_Session
import Definitions.Def_LindbladStructLearn_Admissible
import Definitions.Def_LindbladStructLearn_mass
import Definitions.Def_LindbladStructLearn_b1Norm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal

namespace LindbladStructLearn.Supplement

open LindbladTolerant.Testing LindbladStructLearn

/-- Theorem 5.13 (structure learning of Hamiltonians from real-time evolution; Lewis–Tang–Wright,
*Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256
0af12079…2eb52e), p.48; informal Theorem 1.7, p.5). Let `ε, δ > 0` and `0 < t < 1/(162kg)`. Let
`H = i Σ_P λ_P P` be a `k`-local Hamiltonian with `‖λ‖_B1 ≤ g` and `‖λ‖_∞ ≤ 1`. There is an algorithm
that finds `λ̂` with `‖λ̂ − λ‖_∞ ≤ ε` with probability at least `1 − δ`, using
`t_total = O(g log(n/δ)/ε²)` and classical runtime `O((n^k g²/ε²) log(1/ε) log(n/(δε)))`.

**Formalization Note**
1. The algorithm is one admissible program of the published learner's machine (`Instr`, `branches`),
   chosen after `k` and before `n, g, ε, δ, λ`; its only access to `H` is the `experiment`
   instruction (prepare a Pauli eigenstate, evolve, measure in a Pauli basis) with
   `evo τ = e^(−iHτ) · e^(iHτ)` (`rtChannel`). Input: `n` (integer cell 0), `g, ε, δ` (real cells
   0, 1, 2). Output: `λ̂_P` is the decoded value of the pair `(P, I)`.
2. The evolution time `t` is the algorithm's: every evolution it applies has a duration `τ` with
   `c/g ≤ τ < 1/(162kg)` (the range of the statement, and the time resolution `Θ(1/g)` of Theorem
   1.7). Constants `C, c` depend only on `k`.
3. `log(n/δ)` is `log(2n/δ)`, `log(n/(δε))` is `log(2n/(δ min(ε,1)))`, `log(1/ε)` is
   `1 + log⁺(1/ε)`, and the runtime carries an additive constant. The runtime holds on every run
   (all runs have halted within `N` steps with work at most `N`); the evolution-time and duration
   bounds hold on every reachable configuration. -/
theorem theorem_5_13 (k : ℕ) (hk : 1 ≤ k) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ P : Program, Admissible P ∧
      ∀ n : ℕ, 1 ≤ n → ∀ g : ℝ, 0 < g → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ lam : HIdx n k → ℂ, (∀ P, (lam P).re = 0) → b1Norm (hamVec lam) ≤ g →
        (∀ P, ‖lam P‖ ≤ 1) →
        let evo : ℝ → Super (Qubits n) (Qubits n) := fun τ => rtChannel lam τ
        let s₀ : MState := listInput [(n : ℤ)] [g, ε, δ]
        let N : ℕ := ⌈C * (1 + (n : ℝ) ^ k * g ^ 2 / ε ^ 2) * (1 + max 0 (Real.log (1 / ε))) *
          Real.log (2 * n / (δ * min ε 1))⌉₊
        (∀ s, Reach P n evo N s₀ s → Halted s ∧ s.work ≤ N) ∧
        1 - ENNReal.ofReal δ ≤ mass P n evo N s₀ (fun s => Halted s ∧
          ∀ Q : HIdx n k, ‖decode n k s (Q.1, 0) - lam Q‖ ≤ ε) ∧
        ∀ (M : ℕ) (s : MState), Reach P n evo M s₀ s →
          s.durations.sum ≤ C * g * Real.log (2 * n / δ) / ε ^ 2 ∧
          ∀ τ ∈ s.durations, c / g ≤ τ ∧ τ < 1 / (162 * k * g) := by sorry

end LindbladStructLearn.Supplement
