-- Prove2me | Theorems.Thm_OptQJunta_Supplement_theorem_5_3
-- name    : OptQJunta.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:17:23.194571+00:00
-- url     : https://prove2.me/theorems/049a0314-0814-431f-9d4d-09500d33ed9d
-- title:
--   Theorem 5.3 — junta unitary testing needs $\Omega(\sqrt k/\varepsilon)$ standard-model queries, even controlled
-- statement:
--   Fix integers $k\ge1$ and $n\ge2k$, and fix $0<\varepsilon\le1/4$. Any tester that, given access to an $n$-qubit unitary $U$ in the standard model, distinguishes $U\in\mathcal U_k$ from $\mathrm{dist}_{\mathcal U}(U,\mathcal U_k)\ge\varepsilon$ with success probability at least $2/3$ requires
--
--   $$
--   \Omega\Big(\frac{\sqrt k}{\varepsilon}\Big)
--   $$
--
--   queries. The bound holds even with controlled queries, each applying a coherent choice among $I$, $U$ and $U^\dagger$.
--
--   Together with Theorem 5.2 this shows that the standard-model query complexity of junta unitary testing is $\Theta(\sqrt k/\varepsilon)$ for $n\ge2k$.
--
--   **Formalization Note** One absolute constant $c>0$, fixed before $k,n,\varepsilon$, serves both conjuncts: every uncontrolled standard-model tester and every controlled one makes at least $c\sqrt k/\varepsilon$ queries.
--
--   Differences from the source:
--   - encoding: Ω(·) lower bound on the number of queries → ∃ c > 0, fixed before every parameter, with c·(bound) ≤ count; reason: the paper's Ω(·) has an absolute implicit constant (as in the published Theorem 4.8)
--   - encoding: a quantum query algorithm with ancillas, private randomness, intermediate measurements and adaptivity, counting the worst-case number of queries → the published OptQJunta.SamplerAlg on the n query qubits: oracle-independent unit start state and unitaries on Qubits n × W (W an arbitrary finite workspace), exactly T calls with a fixed pattern, final computational-basis measurement; reason: deferred measurement, purification of the randomness and padding with dummy queries give the same output law on every unitary; an adaptive choice between U and U† is simulated by the alternating pattern at twice the cost, which only rescales the absolute constant (same encoding as the base mission, paper.md decision 3)
--   - encoding: controlled queries: a coherent choice among the identity, the oracle and its inverse → query register Fin 3 × Qubits n with the select oracle |0⟩⟨0|⊗I + |1⟩⟨1|⊗U + |2⟩⟨2|⊗U† (ctrlSel U) and its adjoint; reason: §2.5.2, p.23; the control register is part of the query register, and the adjoint is again such a choice
--   - encoding: distinguishes the two cases with success probability at least 2/3 → acceptance probability ≥ 2/3 on every YES instance and ≤ 1/3 (resp. rejection ≥ 2/3) on every NO instance; nothing off the promise; reason: §2.5 (p.22): a tester must succeed on every promised input and has no requirement outside the promise
--   - encoding: U ∈ 𝒰_T: U = V_T ⊗ I_T̄ with V_T ∈ U(2^{|T|}) → ∃ unitary V on ℂ^{↥T → Bool} with U = liftT T V, ⟨x|U|y⟩ = ⟨x_T|V|y_T⟩·[x_T̄ = y_T̄]; reason: this is the matrix of V_T ⊗ I_T̄ with factors in the original qubit order
--   - encoding: dist_𝒰(U, V) = min over 0 ≤ θ < 2π of ‖e^{iθ}U − V‖₂/√(2N) → infimum over all real θ (distU); reason: e^{iθ} is 2π-periodic, so the set of values is the same, and the minimum is attained
--   - encoding: dist_𝒰(U, 𝒰_k) ≥ ε, an infimum over 𝒰_k → ∀ V ∈ 𝒰_k, ε ≤ dist_𝒰(U, V) (FarU); reason: 𝒰_k is nonempty (it contains I), so the infimum is ≥ ε iff every element is
--   - encoding: qubits indexed by [n] = {1, …, n} → Fin n from 0, basis strings Qubits n = Fin n → Bool; reason: Lean indexing; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 5.3, p.63 (Problem 5.1, p.62; §2.5.2, p.23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_OptQJunta_SamplerAlg
import Definitions.Def_OptQJunta_Supplement_TestsJuntaU

namespace OptQJunta.Supplement

open QAlgorithms OptQJunta

/-- **Theorem 5.3** (Standard-model lower bound for Junta Unitary Testing; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.63). Fix
integers `k ≥ 1` and `n ≥ 2k`, and fix `0 < ε ≤ 1/4`. Any tester that, given access to an `n`-qubit
unitary `U` in the standard model, distinguishes `U ∈ 𝒰_k` from `dist_𝒰(U, 𝒰_k) ≥ ε` with success
probability at least `2/3` requires `Ω(√k/ε)` queries. The bound holds even with controlled queries.

**Formalization Note** `Ω` is an absolute constant `c > 0` fixed before `k`, `n`, `ε`, the same for
both conjuncts: (i) every standard-model tester (queries `U` or `U†` on the `n` query qubits) and
(ii) every tester with controlled queries (`ctrlSel U`, a coherent choice among `I`, `U`, `U†`)
makes at least `c·√k/ε` queries. Testers have an arbitrary finite workspace. -/
theorem theorem_5_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ k n : ℕ, 1 ≤ k → 2 * k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
      (∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (M : SamplerAlg (Qubits n) W T)
          (out : Qubits n × W → Bool), TestsJuntaU M out k ε → c * Real.sqrt k / ε ≤ T) ∧
        (∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (M : SamplerAlg (Fin 3 × Qubits n) W T)
          (out : (Fin 3 × Qubits n) × W → Bool), CTestsJuntaU M out k ε →
            c * Real.sqrt k / ε ≤ T) := by sorry

end OptQJunta.Supplement
