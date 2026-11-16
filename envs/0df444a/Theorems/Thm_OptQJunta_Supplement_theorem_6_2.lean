-- Prove2me | Theorems.Thm_OptQJunta_Supplement_theorem_6_2
-- name    : OptQJunta.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:20:13.523451+00:00
-- url     : https://prove2.me/theorems/da7faf3d-7343-4482-b13f-35ee62f208e0
-- title:
--   Theorem 6.2 — nonadaptive junta channel testing with $O(k/(\varepsilon^2\log(ek)))$ product queries
-- statement:
--   Fix integers $1\le k\le n$ and $0<\varepsilon\le1$. Given channel access to an $n$-qubit channel $\Phi$, there is a nonadaptive quantum algorithm that distinguishes $\Phi\in\mathcal C_k$ from $\mathrm{dist}_{\mathcal C}(\Phi,\mathcal C_k)\ge\varepsilon$ with success probability at least $2/3$ and uses
--
--   $$
--   O\Big(\frac{k}{\varepsilon^2\log(ek)}\Big)
--   $$
--
--   queries, $\log$ base two. Every query acts on a product input state without ancillas and is followed by single-qubit measurements.
--
--   Theorem 6.3 shows that this is optimal in the stated range, even for unitary channels.
--
--   **Formalization Note** The constant is absolute and fixed before $n,k,\varepsilon$. The tester is a `ProductTester`; it accepts with probability at least $2/3$ on every $k$-junta channel and at most $1/3$ on every channel $\varepsilon$-far from all $k$-junta channels.
--
--   Differences from the source:
--   - encoding: O(·) bound on the number of queries/samples → ∃ C > 0, fixed before every parameter, with count ≤ C·(bound); reason: the paper's O(·) has an absolute implicit constant (§2.1 conventions, as in the published Theorems 3.19 and 4.2)
--   - encoding: a nonadaptive algorithm in which every query acts on a product input state without ancillas and is followed by single-qubit measurements → a ProductTester: a random seed fixes, before any query, the product input ⊗_i|ψ_{r,j,i}⟩ and a basis of each qubit for every query j; acceptance probability F(seed, outcomes) ∈ [0, 1]; exactly t queries; reason: nonadaptive (p.22) means inputs and measurements are fixed before the first query; the seed is the private randomness used to fix them
--   - reading: single-qubit measurements → measurement of each output qubit in an orthonormal basis {B|0⟩, B|1⟩}; reason: the stronger of the two readings (projective rather than general single-qubit POVMs); it is the form of Influence-Sample, Lemma 5.4, which the proof uses
--   - encoding: a quantum channel (CPTP map) on n qubits → a superoperator Φ : Matrix → Matrix with IsChannel Φ (the published QAlgorithms.IsChannel: a finite normalized Kraus family); reason: Fact 2.11 (p.15): a superoperator is a channel iff it has such a Kraus representation
--   - encoding: Φ ∈ 𝒞_T: Φ = Ψ_T ⊗ id_T̄ with Ψ_T a channel on the qubits in T → ∃ finite normalized Kraus family L_j on ℂ^{↥T → Bool} with Φ(A) = Σ_j (L_j ⊗ I_T̄) A (L_j ⊗ I_T̄)† for every A; reason: Fact 2.11 for Ψ_T; L_j ⊗ I_T̄ are Kraus operators of Ψ_T ⊗ id_T̄
--   - encoding: dist_𝒞(Φ, 𝒞_k) ≥ ε, an infimum over 𝒞_k → ∀ Ψ ∈ 𝒞_k, ε ≤ dist_𝒞(Φ, Ψ) (FarC), Ψ ranging over all k-junta channels; reason: 𝒞_k is nonempty (it contains the identity channel), so the infimum is ≥ ε iff every element is
--   - encoding: distinguishes the two cases with success probability at least 2/3 → acceptance probability ≥ 2/3 on every YES instance and ≤ 1/3 (resp. rejection ≥ 2/3) on every NO instance; nothing off the promise; reason: §2.5 (p.22): a tester must succeed on every promised input and has no requirement outside the promise
--   - encoding: qubits indexed by [n] = {1, …, n} → Fin n from 0, basis strings Qubits n = Fin n → Bool; reason: Lean indexing; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 6.2, p.72 (Problem 6.1, p.71; Definitions 2.7, 2.17, 2.18, pp.15, 18; §2.5, p.22)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_OptQJunta_Supplement_IsJuntaC
import Definitions.Def_OptQJunta_Supplement_ProductTester

namespace OptQJunta.Supplement

open QAlgorithms

/-- **Theorem 6.2** (Upper bound for Junta Channel Testing; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.72). Fix integers `1 ≤ k ≤ n`
and `0 < ε ≤ 1`. Given channel access to an `n`-qubit channel `Φ`, there is a nonadaptive quantum
algorithm that distinguishes `Φ ∈ 𝒞_k` from `dist_𝒞(Φ, 𝒞_k) ≥ ε` with success probability at least
`2/3` and uses `O(k/(ε² log(ek)))` queries. Every query acts on a product input state without
ancillas and is followed by single-qubit measurements.

**Formalization Note** `O` is an absolute constant `C > 0` fixed before `n`, `k`, `ε`; `log` is base
`2`, `e = exp 1`. A channel is a superoperator with a finite normalized Kraus family (the published
`QAlgorithms.IsChannel`; Fact 2.11, p.15). The algorithm is a `ProductTester` with `t` queries. -/
theorem theorem_6_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (t : ℕ) (R : Type) (_ : Fintype R) (A : ProductTester n t R),
        (t : ℝ) ≤ C * k / (ε ^ 2 * Real.logb 2 (Real.exp 1 * k)) ∧
        ∀ Φ : Superop (Qubits n) (Qubits n), IsChannel Φ →
          (IsJuntaC Φ k → 2 / 3 ≤ A.acc Φ) ∧ (FarC Φ k ε → A.acc Φ ≤ 1 / 3) := by sorry

end OptQJunta.Supplement
