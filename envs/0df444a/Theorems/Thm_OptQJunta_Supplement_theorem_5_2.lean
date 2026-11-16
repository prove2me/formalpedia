-- Prove2me | Theorems.Thm_OptQJunta_Supplement_theorem_5_2
-- name    : OptQJunta.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:16:44.359906+00:00
-- url     : https://prove2.me/theorems/6f0e27e5-3200-467b-b2f4-c37768a3c607
-- title:
--   Theorem 5.2 — junta unitary testing with $O(\sqrt k/\varepsilon)$ standard-model queries
-- statement:
--   Fix integers $1\le k\le n$ and $0<\varepsilon\le1$. Given access to an $n$-qubit unitary $U$ in the standard model (each query applies $U$ or $U^\dagger$), there is a quantum algorithm that distinguishes $U\in\mathcal U_k$ from $\mathrm{dist}_{\mathcal U}(U,\mathcal U_k)\ge\varepsilon$ with success probability at least $2/3$ and uses
--
--   $$
--   O\Big(\frac{\sqrt k}{\varepsilon}\Big)
--   $$
--
--   queries.
--
--   This is the upper half of the $\Theta(\sqrt k/\varepsilon)$ bound for junta unitaries in the standard model; Theorem 5.3 is the matching lower bound.
--
--   **Formalization Note** The constant is absolute and quantified before $n,k,\varepsilon$; the bound is $\sqrt k$ divided by $\varepsilon$. The algorithm may depend on $n,k,\varepsilon$, has a finite workspace, and must succeed on every unitary in the promise.
--
--   Differences from the source:
--   - encoding: O(·) bound on the number of queries/samples → ∃ C > 0, fixed before every parameter, with count ≤ C·(bound); reason: the paper's O(·) has an absolute implicit constant (§2.1 conventions, as in the published Theorems 3.19 and 4.2)
--   - encoding: a quantum query algorithm with ancillas, private randomness, intermediate measurements and adaptivity, counting the worst-case number of queries → the published OptQJunta.SamplerAlg on the n query qubits: oracle-independent unit start state and unitaries on Qubits n × W (W an arbitrary finite workspace), exactly T calls with a fixed pattern, final computational-basis measurement; reason: deferred measurement, purification of the randomness and padding with dummy queries give the same output law on every unitary; an adaptive choice between U and U† is simulated by the alternating pattern at twice the cost, which only rescales the absolute constant (same encoding as the base mission, paper.md decision 3)
--   - encoding: distinguishes the two cases with success probability at least 2/3 → acceptance probability ≥ 2/3 on every YES instance and ≤ 1/3 (resp. rejection ≥ 2/3) on every NO instance; nothing off the promise; reason: §2.5 (p.22): a tester must succeed on every promised input and has no requirement outside the promise
--   - encoding: U ∈ 𝒰_T: U = V_T ⊗ I_T̄ with V_T ∈ U(2^{|T|}) → ∃ unitary V on ℂ^{↥T → Bool} with U = liftT T V, ⟨x|U|y⟩ = ⟨x_T|V|y_T⟩·[x_T̄ = y_T̄]; reason: this is the matrix of V_T ⊗ I_T̄ with factors in the original qubit order
--   - encoding: dist_𝒰(U, V) = min over 0 ≤ θ < 2π of ‖e^{iθ}U − V‖₂/√(2N) → infimum over all real θ (distU); reason: e^{iθ} is 2π-periodic, so the set of values is the same, and the minimum is attained
--   - encoding: dist_𝒰(U, 𝒰_k) ≥ ε, an infimum over 𝒰_k → ∀ V ∈ 𝒰_k, ε ≤ dist_𝒰(U, V) (FarU); reason: 𝒰_k is nonempty (it contains I), so the infimum is ≥ ε iff every element is
--   - encoding: qubits indexed by [n] = {1, …, n} → Fin n from 0, basis strings Qubits n = Fin n → Bool; reason: Lean indexing; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 5.2, p.62 (Problem 5.1, p.62; Definitions 2.15, 2.16, p.17; §2.5.2, p.23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_OptQJunta_SamplerAlg
import Definitions.Def_OptQJunta_Supplement_TestsJuntaU

namespace OptQJunta.Supplement

open QAlgorithms OptQJunta

/-- **Theorem 5.2** (Standard-model upper bound for Junta Unitary Testing; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.62). Fix
integers `1 ≤ k ≤ n` and `0 < ε ≤ 1`. Given access to an `n`-qubit unitary `U` in the standard
model, there is a quantum algorithm that distinguishes `U ∈ 𝒰_k` from `dist_𝒰(U, 𝒰_k) ≥ ε` with
success probability at least `2/3` and uses `O(√k/ε)` queries.

**Formalization Note** `O` is an absolute constant `C > 0` fixed before `n`, `k`, `ε`. The bound is
`√k` divided by `ε`. The algorithm (its finite workspace `W`, call pattern of `U`/`U†`, unitaries,
start state and output map) may depend on `n`, `k`, `ε`, and must succeed on every unitary in the
promise (`TestsJuntaU`). -/
theorem theorem_5_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (T : ℕ)
        (M : SamplerAlg (Qubits n) W T) (out : Qubits n × W → Bool),
        (T : ℝ) ≤ C * Real.sqrt k / ε ∧ TestsJuntaU M out k ε := by sorry

end OptQJunta.Supplement
