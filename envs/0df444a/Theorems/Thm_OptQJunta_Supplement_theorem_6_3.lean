-- Prove2me | Theorems.Thm_OptQJunta_Supplement_theorem_6_3
-- name    : OptQJunta.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:20:56.528683+00:00
-- url     : https://prove2.me/theorems/4278ed72-9f05-4925-8f34-7b6e7a56630b
-- title:
--   Theorem 6.3 — junta channel testing needs $\Omega(k/(\varepsilon^2\log k))$ queries, even for unitary channels
-- statement:
--   Fix a sufficiently large integer $k$, an integer $n\ge2k$, and $2^{-k/16}\le\varepsilon\le1/16$. Any tester that, given channel access to an $n$-qubit channel $\Phi$, distinguishes $\Phi\in\mathcal C_k$ from $\mathrm{dist}_{\mathcal C}(\Phi,\mathcal C_k)\ge\varepsilon$ with success probability at least $2/3$ requires
--
--   $$
--   \Omega\Big(\frac{k}{\varepsilon^2\log k}\Big)
--   $$
--
--   queries, $\log$ base two. The bound holds even when $\Phi$ is promised to be a unitary channel.
--
--   The NO condition measures distance to all $k$-junta channels, nonunitary ones included.
--
--   **Formalization Note** The constant $c>0$ and the threshold $K$ are absolute and fixed before $k,n,\varepsilon$. The tester is a channel-access algorithm (`ChanAlg`) that is only required to succeed on unitary channels $\Phi_U$: accept with probability at least $2/3$ when $\Phi_U\in\mathcal C_k$ and reject with probability at least $2/3$ when $\mathrm{dist}_{\mathcal C}(\Phi_U,\mathcal C_k)\ge\varepsilon$. A tester that succeeds on all channels satisfies this, so the statement contains the general lower bound.
--
--   Differences from the source:
--   - encoding: Ω(·) lower bound on the number of queries → ∃ c > 0, fixed before every parameter, with c·(bound) ≤ count; reason: the paper's Ω(·) has an absolute implicit constant (as in the published Theorem 4.8)
--   - encoding: for a sufficiently large integer k → ∃ K, fixed before k, n, ε, with the claim for every k ≥ K; reason: standard reading of 'sufficiently large'; K does not depend on n or ε
--   - encoding: a tester with channel access (ancillas, interleaving channels, randomness, intermediate measurements, adaptivity, accepting POVM; worst-case number of queries) → ChanAlg: oracle-independent unit start state and unitaries on Qubits n × W (W an arbitrary finite workspace), exactly T queries Φ ⊗ I_W, final computational-basis measurement; reason: Stinespring and Naimark dilation into a larger finite workspace and padding give the same acceptance probability on every channel (§5.4.2, p.67)
--   - encoding: the bound holds even when Φ is promised to be a unitary channel → the success hypotheses are required only for unitary channels Φ_U, with the NO condition dist_𝒞(Φ_U, 𝒞_k) ≥ ε over all k-junta channels; reason: this is the paper's 'even' clause; a tester succeeding on all channels meets the weaker hypothesis, so the general bound follows
--   - encoding: Φ ∈ 𝒞_T: Φ = Ψ_T ⊗ id_T̄ with Ψ_T a channel on the qubits in T → ∃ finite normalized Kraus family L_j on ℂ^{↥T → Bool} with Φ(A) = Σ_j (L_j ⊗ I_T̄) A (L_j ⊗ I_T̄)† for every A; reason: Fact 2.11 for Ψ_T; L_j ⊗ I_T̄ are Kraus operators of Ψ_T ⊗ id_T̄
--   - encoding: dist_𝒞(Φ, 𝒞_k) ≥ ε, an infimum over 𝒞_k → ∀ Ψ ∈ 𝒞_k, ε ≤ dist_𝒞(Φ, Ψ) (FarC), Ψ ranging over all k-junta channels; reason: 𝒞_k is nonempty (it contains the identity channel), so the infimum is ≥ ε iff every element is
--   - encoding: distinguishes the two cases with success probability at least 2/3 → acceptance probability ≥ 2/3 on every YES instance and ≤ 1/3 (resp. rejection ≥ 2/3) on every NO instance; nothing off the promise; reason: §2.5 (p.22): a tester must succeed on every promised input and has no requirement outside the promise
--   - encoding: qubits indexed by [n] = {1, …, n} → Fin n from 0, basis strings Qubits n = Fin n → Bool; reason: Lean indexing; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 6.3, p.72 (Problem 6.1, p.71; §2.5.3, p.23; Definitions 2.17, 2.18, p.18)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_OptQJunta_Supplement_IsJuntaC
import Definitions.Def_OptQJunta_Supplement_ChanAlg

namespace OptQJunta.Supplement

open QAlgorithms

/-- **Theorem 6.3** (Lower bound for Junta Channel Testing; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.72). Fix a sufficiently large
integer `k`, an integer `n ≥ 2k`, and `2^{−k/16} ≤ ε ≤ 1/16`. Any tester that, given channel access to
an `n`-qubit channel `Φ`, distinguishes `Φ ∈ 𝒞_k` from `dist_𝒞(Φ, 𝒞_k) ≥ ε` with success probability
at least `2/3` requires `Ω(k/(ε² log k))` queries. The bound holds even when `Φ` is promised to be a
unitary channel.

**Formalization Note** `Ω` is an absolute constant `c > 0` and "sufficiently large" a threshold `K`,
both fixed before `k`, `n`, `ε`; `log` is base `2`. The tester is a channel-access algorithm
(`ChanAlg`, arbitrary finite workspace) required to succeed only on unitary channels `Φ_U`: accept
with probability `≥ 2/3` if `Φ_U ∈ 𝒞_k`, reject with probability `≥ 2/3` if `dist_𝒞(Φ_U, 𝒞_k) ≥ ε`,
the distance ranging over all `k`-junta channels. Every tester that succeeds on all channels
satisfies this hypothesis, so the statement contains the general lower bound. -/
theorem theorem_6_3 :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ n : ℕ, 2 * k ≤ n →
      ∀ ε : ℝ, (2 : ℝ) ^ (-(k : ℝ) / 16) ≤ ε → ε ≤ 1 / 16 →
        ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (A : ChanAlg n W T)
          (out : Qubits n × W → Bool),
          (∀ U : Matrix.unitaryGroup (Qubits n) ℂ,
              IsJuntaC (unitChan (U : Matrix (Qubits n) (Qubits n) ℂ)) k →
                2 / 3 ≤ A.outputProb (unitChan (U : Matrix (Qubits n) (Qubits n) ℂ)) out true) →
          (∀ U : Matrix.unitaryGroup (Qubits n) ℂ,
              FarC (unitChan (U : Matrix (Qubits n) (Qubits n) ℂ)) k ε →
                2 / 3 ≤ A.outputProb (unitChan (U : Matrix (Qubits n) (Qubits n) ℂ)) out false) →
          c * k / (ε ^ 2 * Real.logb 2 k) ≤ T := by sorry

end OptQJunta.Supplement
