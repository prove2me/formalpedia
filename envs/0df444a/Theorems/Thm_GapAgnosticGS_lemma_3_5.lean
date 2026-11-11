-- Prove2me | Theorems.Thm_GapAgnosticGS_lemma_3_5
-- name    : GapAgnosticGS.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:54.979441+00:00
-- url     : https://prove2.me/theorems/942a2d63-990e-43f9-8aba-b79d01be4dc9
-- title:
--   Lemma 3.5 — a gapped threshold test per hidden branch with $O(\eta^{-1}\log(1/a))$ queries
-- statement:
--   There is an absolute constant $C_0$ with the following property. Let $n\ge0$, let $A$ be an arm register with known $|0\rangle_A$ and reward projector $\Pi$, and fix a threshold $\tau\in[0,1]$, a gap $\eta\in(0,1/2)$ and an amplitude error $a\in(0,1/4)$. There is one oracle circuit with
--
--   $$T\le C_0\,\frac1\eta\log\frac1a$$
--
--   controlled queries to $E$ or $E^\dagger$, built without knowledge of $E$, whose unitary $\mathrm{GTT}(\eta,a;\tau)$ on $I$, $A$ and auxiliary registers $C,P$ is, for **every** hidden-basis environment $E$ with this $|0\rangle_A$ and $\Pi$, a gapped threshold test:
--
--   1. every subspace $\mathcal H_j\otimes\mathcal H_{CP}$ is invariant;
--   2. for every unit $|\psi_j\rangle\in\mathcal H_j$,
--   $$p_j\ge\tau+\eta\implies\|(I_{IAP}\otimes\langle1|_C)\,\mathrm{GTT}\,|\psi_j\rangle|0\rangle_{CP}\|\le a,\qquad p_j\le\tau-\eta\implies\|(I_{IAP}\otimes\langle0|_C)\,\mathrm{GTT}\,|\psi_j\rangle|0\rangle_{CP}\|\le a .$$
--
--   $C=0$ is the high-reward outcome. The test is branch-preserving, which is what allows thresholds to be compared in a hidden basis.
--
--   Differences from the source:
--   - reading: O((1/η) log(1/a)) queries → T ≤ C₀ (1/η) log(1/a) with one absolute C₀ chosen before every other quantity; reason: the standard meaning of O(·)
--   - reading: a unitary GTT(η, a; τ) … constructed using queries to E and E† → one fixed-length oracle circuit, chosen before E (depending only on n, A, |0⟩_A, Π, τ, η, a), that is a GTT for every environment; reason: the learner does not know E; the construction only queries it
--   - encoding: for every |ψ_j⟩_IA ∈ H_j → for every unit vector ψ ∈ H_j; reason: kets denote states (the overview, p.7: 'any normalized input'); by linearity equivalent to the bound a‖ψ‖ for every ψ
--   - encoding: auxiliary registers C and P initialized to |0⟩ → registers Bool × Bool × Fin (m+1): the query-control qubit, the flag C and the workspace P, all starting in 0; reason: the query-control qubit is an auxiliary register of the circuit
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.5 (Threshold test for a single branch), p.10 (PDF p.11)

import Definitions.Def_GapAgnosticGS_IsGTT
import Definitions.Def_GapAgnosticGS_OracleCircuit_unitary

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.5 (Threshold test for a single branch), p.10 (PDF p.11): "Consider a HidQMAB
environment E as in Definition 1.4 with the branch subspaces H_j as in Lemma 3.4. Fix a threshold
τ ∈ [0, 1], a gap η ∈ (0, 1/2), and an amplitude error a ∈ (0, 1/4). There is a unitary
GTT(η, a; τ) acting on the selector register I, the arm register A, and auxiliary registers C and
P, which can be constructed using O((1/η) log(1/a)) queries to E and E† such that: (i) every
subspace H_j ⊗ H_CP is invariant; (ii) for every |ψ_j⟩_IA ∈ H_j,
p_j ≥ τ + η ⟹ ‖(I_IAP ⊗ ⟨1|_C) GTT(η, a; τ)(|ψ_j⟩_IA|0⟩_CP)‖ ≤ a,
p_j ≤ τ − η ⟹ ‖(I_IAP ⊗ ⟨0|_C) GTT(η, a; τ)(|ψ_j⟩_IA|0⟩_CP)‖ ≤ a.
Here C = 0 denotes the high-reward outcome."

There is an absolute constant `C₀` such that for every `n`, arm register `A` with known `|0⟩_A`
and projector `Π`, and every `τ ∈ [0,1]`, `η ∈ (0,1/2)`, `a ∈ (0,1/4)`, one oracle circuit with
`T ≤ C₀ (1/η) log(1/a)` controlled queries to `E` or `E†`, fixed before the environment, is, for
every environment `E` with that `|0⟩_A` and `Π`, a gapped threshold test `GTT(η, a; τ)`
(`IsGTT`: unitary, (i) and (ii)).

**Formalization Note.** O(·) is an absolute constant `C₀`, chosen before all other data. The
circuit's auxiliary registers are `Bool × Bool × Fin (m+1)`: the query-control qubit, the flag `C`
and the workspace `P`, all starting in `0`; it depends on `n, A, a₀, Π, τ, η, a` only, never on
`E` ("constructed using queries to E and E†"). -/
theorem lemma_3_5 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] (a₀ : A) (Prj : Matrix A A ℂ) (τ η a : ℝ),
      τ ∈ Set.Icc 0 1 → η ∈ Set.Ioo 0 (1 / 2) → a ∈ Set.Ioo 0 (1 / 4) →
    ∃ (m T : ℕ) (circ : OracleCircuit (Fin n × A) (Bool × Fin (m + 1)) T),
      (T : ℝ) ≤ C₀ * (1 / η) * Real.log (1 / a) ∧
      ∀ Env : HidEnv n A a₀ Prj,
        IsGTT Env ((false, false, 0) : Bool × Bool × Fin (m + 1)) (fun r => r.2.1)
          (circ.unitary Env.E) η τ a := by sorry

end GapAgnosticGS
