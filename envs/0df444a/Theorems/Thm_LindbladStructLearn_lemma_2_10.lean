-- Prove2me | Theorems.Thm_LindbladStructLearn_lemma_2_10
-- name    : LindbladStructLearn.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:05:39.142715+00:00
-- url     : https://prove2.me/theorems/59c0482f-35f6-44b0-84f7-ef26e733ba75
-- title:
--   Lemma 2.10 — Algorithm 1 learns all local Fourier coefficients to ε with $O(C^k\log(n/\delta)/\varepsilon^2)$ queries in time $O(Mn^k)$
-- statement:
--   There is an absolute constant $C > 0$ such that for every locality $k \ge 1$ there are a constant $C'$ and a program (Algorithm 1) on the learner's machine with the following guarantee. For every $n \ge 1$, $\varepsilon > 0$, $\delta \in (0,1)$, every natural number
--
--   $$M \ge \frac{C^k\log(2n/\delta)}{\varepsilon^2},$$
--
--   and every $n$-qubit quantum channel $\Phi$, the program run on input $(n, M, \varepsilon, \delta)$, whose experiments apply $\Phi$:
--
--   1. halts on every run within $\lceil C' M n^k\rceil$ steps (time $O(Mn^k)$);
--   2. with probability at least $1-\delta$ outputs estimates with $|\widehat E_{P_1,P_2} - \widehat\Phi_{\mathrm{loc}}(P_1,P_2)| \le \varepsilon$ for all $P_1, P_2 \in \mathcal P_n$ with $s_{\overline P} \le k$;
--   3. performs at most $M$ queries to $\Phi$ on every run.
--
--   The lemma is how the algorithm estimates the expectation values $E(\lambda)$ of the unknown dynamics.
--
--   Differences from the source:
--   - reading: M = Θ(C^k log(n/δ)/ε²) → every natural M ≥ C^k log(2n/δ)/ε²; reason: Θ for an algorithm parameter read as any M at least the bound (stronger than one M); log(2n/δ) instead of log(n/δ), which tends to 0 at n = 1, δ → 1, where a fixed small number of samples cannot be ε-accurate
--   - reading: error parameter δ > 0 → δ ∈ (0,1); reason: for δ ≥ 1 the probability claim is empty and log(n/δ) can be ≤ 0, so the query and time bounds would be 0
--   - reading: Algorithm 1 runs in time O(Mn^k); the outputs of Algorithm 1 → some admissible program on the learner's machine (real RAM + coin + Pauli experiments) whose every run halts within ⌈C'·M·n^k⌉ steps, C' depending on k; reason: the paper gives Algorithm 1 in pseudocode without a machine model; the constant of O(·) may depend on the locality k
--   - encoding: using M queries to the channel Φ → every reachable configuration has applied at most M experiments; reason: query count as the length of the experiment record
--   - encoding: quantum channel Φ → completely positive (on every finite ancilla) and trace-preserving superoperator; reason: definition of a channel
--   - encoding: n qubits → n ≥ 1; reason: excludes only the degenerate system with no qubit, where log(n/δ) is undefined
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Lemma 2.10, p.18; Algorithm 1, p.17

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_Admissible
import Definitions.Def_LindbladStructLearn_Reach
import Definitions.Def_LindbladStructLearn_mass
import Definitions.Def_LindbladStructLearn_Halted
import Definitions.Def_LindbladStructLearn_decode
import Definitions.Def_LindbladStructLearn_alg1Input
import Definitions.Def_LindbladStructLearn_IsChannel
import Definitions.Def_LindbladStructLearn_locFourier
import Definitions.Def_LindbladStructLearn_pairSupport

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Lemma 2.10 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.18; Algorithm 1, p.17): there is an absolute constant `C > 0` such that,
for every locality `k ≥ 1`, Algorithm 1 run with any `M ≥ C^k log(2n/δ)/ε²` outputs, with
probability at least `1 − δ`, estimates `Ê_(P₁,P₂)` with `|Ê_(P₁,P₂) − Φ̂_loc(P₁,P₂)| ≤ ε` for all
`P₁, P₂ ∈ 𝒫_n` with `s_P̄ ≤ k`, using `M` queries to the channel `Φ`, in time `O(M n^k)`.

**Formalization Note** "Algorithm 1" is the witness program on the learner's machine
(`Instr`, `branches`): its only quantum access is the `experiment` instruction with the channel
`Φ` (`evo` constant). Input: `n, M` in integer cells, `ε, δ` in real cells (`alg1Input`); output:
the records decoded by `decode` (pairs with `P₁ = I` included). `M = Θ(C^k log(n/δ)/ε²)` is read
as "every `M ≥ C^k log(2n/δ)/ε²`"; `log(2n/δ)` replaces `log(n/δ)`, which tends to `0` at `n = 1`,
`δ → 1`. The `O(M n^k)` constant `C'` may depend on `k`. The time bound holds on every run (all
runs have halted within `⌈C' M n^k⌉` steps, with total work at most that), and every reachable
configuration has made at most `M` queries. -/
theorem lemma_2_10 :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∃ C' : ℝ, 0 < C' ∧ ∃ P : Program, Admissible P ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ M : ℕ,
      C ^ k * Real.log (2 * n / δ) / ε ^ 2 ≤ M →
      ∀ Φ : Super (Qubits n) (Qubits n), IsChannel Φ →
        let evo : ℝ → Super (Qubits n) (Qubits n) := fun _ => Φ
        let N : ℕ := ⌈C' * M * (n : ℝ) ^ k⌉₊
        (∀ s, Reach P n evo N (alg1Input n M ε δ) s → Halted s ∧ s.work ≤ N) ∧
        1 - ENNReal.ofReal δ ≤ mass P n evo N (alg1Input n M ε δ) (fun s => Halted s ∧
          ∀ Q : Pauli n × Pauli n, (pairSupport Q).card ≤ k →
            ‖decode n k s Q - locFourier Φ Q‖ ≤ ε) ∧
        ∀ (M' : ℕ) (s : MState), Reach P n evo M' (alg1Input n M ε δ) s →
          s.durations.length ≤ M := by sorry

end LindbladStructLearn
