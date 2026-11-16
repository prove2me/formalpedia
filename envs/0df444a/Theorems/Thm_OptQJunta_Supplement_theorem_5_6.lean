-- Prove2me | Theorems.Thm_OptQJunta_Supplement_theorem_5_6
-- name    : OptQJunta.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:18:54.302233+00:00
-- url     : https://prove2.me/theorems/e89ea8d7-2c1a-4230-b785-1a30e2e1bfc7
-- title:
--   Theorem 5.6 — forward-only junta unitary testing needs $\Omega(k/(\varepsilon^2\log k))$ queries
-- statement:
--   Fix a sufficiently large integer $k$, an integer $n\ge2k$, and $2^{-k/16}\le\varepsilon\le1/16$. Any tester that, given forward-only access to an $n$-qubit unitary $U$, distinguishes $U\in\mathcal U_k$ from $\mathrm{dist}_{\mathcal U}(U,\mathcal U_k)\ge\varepsilon$ with success probability at least $2/3$ requires
--
--   $$
--   \Omega\Big(\frac{k}{\varepsilon^2\log k}\Big)
--   $$
--
--   queries, $\log$ base two.
--
--   The bound holds against adaptive testers with arbitrary ancillas and matches Theorem 5.5 in this range: without $U^\dagger$, junta unitary testing loses the quadratic speedup of the standard model.
--
--   **Formalization Note** The constant $c>0$ and the threshold $K$ for "sufficiently large" are absolute and fixed before $k,n,\varepsilon$. A forward-only tester is a `SamplerAlg` every slot of which calls $U$.
--
--   Differences from the source:
--   - encoding: Ω(·) lower bound on the number of queries → ∃ c > 0, fixed before every parameter, with c·(bound) ≤ count; reason: the paper's Ω(·) has an absolute implicit constant (as in the published Theorem 4.8)
--   - encoding: for a sufficiently large integer k → ∃ K, fixed before k, n, ε, with the claim for every k ≥ K; reason: standard reading of 'sufficiently large'; K does not depend on n or ε
--   - encoding: a quantum query algorithm with ancillas, private randomness, intermediate measurements and adaptivity, counting the worst-case number of queries → the published OptQJunta.SamplerAlg on the n query qubits: oracle-independent unit start state and unitaries on Qubits n × W (W an arbitrary finite workspace), exactly T calls with a fixed pattern, final computational-basis measurement; reason: deferred measurement, purification of the randomness and padding with dummy queries give the same output law on every unitary; an adaptive choice between U and U† is simulated by the alternating pattern at twice the cost, which only rescales the absolute constant (same encoding as the base mission, paper.md decision 3)
--   - encoding: forward-only access: one query applies U → a SamplerAlg with every slot calling U (IsForwardOnly: dir i = false for all i); reason: §2.5.2, p.23
--   - encoding: distinguishes the two cases with success probability at least 2/3 → acceptance probability ≥ 2/3 on every YES instance and ≤ 1/3 (resp. rejection ≥ 2/3) on every NO instance; nothing off the promise; reason: §2.5 (p.22): a tester must succeed on every promised input and has no requirement outside the promise
--   - encoding: U ∈ 𝒰_T: U = V_T ⊗ I_T̄ with V_T ∈ U(2^{|T|}) → ∃ unitary V on ℂ^{↥T → Bool} with U = liftT T V, ⟨x|U|y⟩ = ⟨x_T|V|y_T⟩·[x_T̄ = y_T̄]; reason: this is the matrix of V_T ⊗ I_T̄ with factors in the original qubit order
--   - encoding: dist_𝒰(U, V) = min over 0 ≤ θ < 2π of ‖e^{iθ}U − V‖₂/√(2N) → infimum over all real θ (distU); reason: e^{iθ} is 2π-periodic, so the set of values is the same, and the minimum is attained
--   - encoding: dist_𝒰(U, 𝒰_k) ≥ ε, an infimum over 𝒰_k → ∀ V ∈ 𝒰_k, ε ≤ dist_𝒰(U, V) (FarU); reason: 𝒰_k is nonempty (it contains I), so the infimum is ≥ ε iff every element is
--   - encoding: qubits indexed by [n] = {1, …, n} → Fin n from 0, basis strings Qubits n = Fin n → Bool; reason: Lean indexing; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 5.6, p.64 (Problem 5.1, p.62; §2.5.2, p.23)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_OptQJunta_SamplerAlg
import Definitions.Def_OptQJunta_Supplement_TestsJuntaU

namespace OptQJunta.Supplement

open QAlgorithms OptQJunta

/-- **Theorem 5.6** (Forward-only lower bound for Junta Unitary Testing; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.64). Fix a
sufficiently large integer `k`, an integer `n ≥ 2k`, and `2^{−k/16} ≤ ε ≤ 1/16`. Any tester that,
given forward-only access to an `n`-qubit unitary `U`, distinguishes `U ∈ 𝒰_k` from
`dist_𝒰(U, 𝒰_k) ≥ ε` with success probability at least `2/3` requires `Ω(k/(ε² log k))` queries.

**Formalization Note** `Ω` is an absolute constant `c > 0` and "sufficiently large" a threshold `K`,
both fixed before `k`, `n`, `ε`; `log` is base `2`. Testers are adaptive, with an arbitrary finite
workspace (ancillas); forward-only means every query slot calls `U` (`IsForwardOnly`). -/
theorem theorem_5_6 :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ ε : ℝ, (2 : ℝ) ^ (-(k : ℝ) / 16) ≤ ε → ε ≤ 1 / 16 →
        ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (M : SamplerAlg (Qubits n) W T)
          (out : Qubits n × W → Bool), IsForwardOnly M → TestsJuntaU M out k ε →
            c * k / (ε ^ 2 * Real.logb 2 k) ≤ T := by sorry

end OptQJunta.Supplement
