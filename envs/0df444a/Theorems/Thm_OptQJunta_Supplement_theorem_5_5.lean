-- Prove2me | Theorems.Thm_OptQJunta_Supplement_theorem_5_5
-- name    : OptQJunta.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:18:14.995193+00:00
-- url     : https://prove2.me/theorems/6f1f32a8-4598-4db2-bb87-e6589892e50d
-- title:
--   Theorem 5.5 — nonadaptive forward-only junta unitary testing with $O(k/(\varepsilon^2\log(ek)))$ product queries
-- statement:
--   Fix integers $1\le k\le n$ and $0<\varepsilon\le1$. Given forward-only access to an $n$-qubit unitary $U$, there is a nonadaptive quantum algorithm that distinguishes $U\in\mathcal U_k$ from $\mathrm{dist}_{\mathcal U}(U,\mathcal U_k)\ge\varepsilon$ with success probability at least $2/3$ and uses
--
--   $$
--   O\Big(\frac{k}{\varepsilon^2\log(ek)}\Big)
--   $$
--
--   queries, $\log$ base two. Every query acts on a product input state without ancillas and is followed by single-qubit measurements.
--
--   Theorem 5.6 shows that this is optimal up to the difference between $\log(ek)$ and $\log k$, even against adaptive testers with ancillas.
--
--   **Formalization Note** The constant is absolute and fixed before $n,k,\varepsilon$. A forward query on an ancilla-free input $\rho$ returns $U\rho U^\dagger$, so the tester is a `ProductTester` run on the unitary channel $\Phi_U$; it accepts with probability at least $2/3$ on YES and at most $1/3$ on NO.
--
--   Differences from the source:
--   - encoding: O(·) bound on the number of queries/samples → ∃ C > 0, fixed before every parameter, with count ≤ C·(bound); reason: the paper's O(·) has an absolute implicit constant (§2.1 conventions, as in the published Theorems 3.19 and 4.2)
--   - encoding: a nonadaptive algorithm in which every query acts on a product input state without ancillas and is followed by single-qubit measurements → a ProductTester: a random seed fixes, before any query, the product input ⊗_i|ψ_{r,j,i}⟩ and a basis of each qubit for every query j; acceptance probability F(seed, outcomes) ∈ [0, 1]; exactly t queries; reason: nonadaptive (p.22) means inputs and measurements are fixed before the first query; the seed is the private randomness used to fix them
--   - reading: single-qubit measurements → measurement of each output qubit in an orthonormal basis {B|0⟩, B|1⟩}; reason: the stronger of the two readings (projective rather than general single-qubit POVMs); it is the form of Influence-Sample, Lemma 5.4, which the proof uses
--   - encoding: one forward query to U on an ancilla-free input state ρ → the unitary channel Φ_U(ρ) = UρU† applied to the input state (unitChan U); reason: Eq. (14), p.23
--   - encoding: distinguishes the two cases with success probability at least 2/3 → acceptance probability ≥ 2/3 on every YES instance and ≤ 1/3 (resp. rejection ≥ 2/3) on every NO instance; nothing off the promise; reason: §2.5 (p.22): a tester must succeed on every promised input and has no requirement outside the promise
--   - encoding: U ∈ 𝒰_T: U = V_T ⊗ I_T̄ with V_T ∈ U(2^{|T|}) → ∃ unitary V on ℂ^{↥T → Bool} with U = liftT T V, ⟨x|U|y⟩ = ⟨x_T|V|y_T⟩·[x_T̄ = y_T̄]; reason: this is the matrix of V_T ⊗ I_T̄ with factors in the original qubit order
--   - encoding: dist_𝒰(U, V) = min over 0 ≤ θ < 2π of ‖e^{iθ}U − V‖₂/√(2N) → infimum over all real θ (distU); reason: e^{iθ} is 2π-periodic, so the set of values is the same, and the minimum is attained
--   - encoding: dist_𝒰(U, 𝒰_k) ≥ ε, an infimum over 𝒰_k → ∀ V ∈ 𝒰_k, ε ≤ dist_𝒰(U, V) (FarU); reason: 𝒰_k is nonempty (it contains I), so the infimum is ≥ ε iff every element is
--   - encoding: qubits indexed by [n] = {1, …, n} → Fin n from 0, basis strings Qubits n = Fin n → Bool; reason: Lean indexing; same instances
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), Theorem 5.5, p.64 (§2.5, p.22; §2.5.2, Eq. (14), p.23; Lemma 5.4, p.63)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_OptQJunta_Supplement_IsJuntaU
import Definitions.Def_OptQJunta_Supplement_IsJuntaC
import Definitions.Def_OptQJunta_Supplement_ProductTester

namespace OptQJunta.Supplement

open QAlgorithms

/-- **Theorem 5.5** (Forward-only upper bound for Junta Unitary Testing; Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, p.64). Fix integers
`1 ≤ k ≤ n` and `0 < ε ≤ 1`. Given forward-only access to an `n`-qubit unitary `U`, there is a
nonadaptive quantum algorithm that distinguishes `U ∈ 𝒰_k` from `dist_𝒰(U, 𝒰_k) ≥ ε` with success
probability at least `2/3` and uses `O(k/(ε² log(ek)))` queries. Every query acts on a product input
state without ancillas and is followed by single-qubit measurements.

**Formalization Note** `O` is an absolute constant `C > 0` fixed before `n`, `k`, `ε`; `log` is base
`2`, `e = exp 1`. The algorithm is a `ProductTester` with `t` queries; one forward query to `U` on an
ancilla-free input `ρ` returns `U ρ U†` (Eq. (14), p.23), i.e. the unitary channel `Φ_U`. It accepts
with probability `≥ 2/3` on every `U ∈ 𝒰_k` and `≤ 1/3` on every `U` with `dist_𝒰(U, 𝒰_k) ≥ ε`. -/
theorem theorem_5_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ (t : ℕ) (R : Type) (_ : Fintype R) (A : ProductTester n t R),
        (t : ℝ) ≤ C * k / (ε ^ 2 * Real.logb 2 (Real.exp 1 * k)) ∧
        ∀ U : Matrix.unitaryGroup (Qubits n) ℂ,
          (IsJuntaU (U : Matrix (Qubits n) (Qubits n) ℂ) k →
              2 / 3 ≤ A.acc (unitChan (U : Matrix (Qubits n) (Qubits n) ℂ))) ∧
            (FarU (U : Matrix (Qubits n) (Qubits n) ℂ) k ε →
              A.acc (unitChan (U : Matrix (Qubits n) (Qubits n) ℂ)) ≤ 1 / 3) := by sorry

end OptQJunta.Supplement
