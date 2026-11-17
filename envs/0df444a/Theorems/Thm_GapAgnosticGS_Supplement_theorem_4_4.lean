-- Prove2me | Theorems.Thm_GapAgnosticGS_Supplement_theorem_4_4
-- name    : GapAgnosticGS.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:33:51.446434+00:00
-- url     : https://prove2.me/theorems/5833e4c2-7eee-4de7-94bb-a97ea2837031
-- title:
--   Theorem 4.4 — gap-free guided-state PAC preparation: reward $\ge p_\star-\varepsilon$ with $\tilde O(\gamma^{-1}\sqrt{L(\varepsilon)})$ expected queries
-- statement:
--   Let $E$ be a hidden-basis environment with $n\ge1$ arms, rewards $p_j$ and best reward $p_\star$ (best arms may be degenerate), and $U_I$ a unitary with $|\psi_I\rangle=U_I|0\rangle$ satisfying (7), $\|\Pi_\star|\psi_I\rangle\|\ge\gamma>0$. The learner has controlled access to $E$, $U_I$ and their inverses.
--
--   There are absolute constants $C>0$ and $K$ such that for every $n\ge1$, arm register with known $|0\rangle_A$ and $\Pi$, $\gamma>0$, $\varepsilon\in(0,1/8)$ and $\delta\in(0,1/3)$ there is one algorithm which, for every such $E$ and $U_I$, outputs with probability at least $1-\delta$ a selector state $\rho$ with
--
--   $$
--   \mathrm{reward}(\rho)\ge p_\star-\varepsilon,
--   $$
--
--   using in expectation at most
--
--   $$
--   C\,\frac1\gamma\sqrt{L(\varepsilon,\{p_j\},|\psi_I\rangle)}\,\Big(\log\frac1{\varepsilon\gamma\delta}\Big)^K
--   $$
--
--   controlled queries to $E$, $U_I$ and their inverses. Here $\mathrm{reward}(\rho)=\operatorname{tr}((I\otimes\Pi)E(\rho\otimes|0\rangle\langle0|)E^\dagger)$ is the reward of the output state (Problem 3.12).
--
--   This is the bandit form of warm-start ground-state preparation without a gap bound; through the Hamiltonian bandit of Lemma 3.1 it yields Theorem 1.3.
--
--   **Formalization Note** The two oracles are the direct sum `oracleSum Env.E UI`; $\rho$ is the reduced state of the output register $\mathbb C^n$ (the selector register).
--
--   Differences from the source:
--   - encoding: queries to the first oracle and the same order of queries to the second → queries to the direct sum oracleSum of the two unitaries; reason: one query to the sum is one query to each, and one query to either is one query to the sum, so the two counts agree up to a factor 2
--   - encoding: (7): ‖Π⋆|ψI⟩‖ ≥ γ with Π⋆ = Σ_{j: p_j = p⋆} |ϕ_j⟩⟨ϕ_j| → γ² ≤ Σ_{j: p_j = p⋆} |⟨ϕ_j, U_I|0⟩⟩|² for a unitary U_I on ℂⁿ, γ > 0; reason: ‖Π⋆ψ‖² = Σ_{j: p_j = p⋆} |c_j|² in the hidden orthonormal basis; both sides nonnegative
--   - reading: "uses O((1/γ)√L(ε, {pj}, |ψI⟩) polylog(1/(εγδ))) queries" → expected queries ≤ C (1/γ) √L(ε) · log^K(1/(εγδ)); reason: the proof ends "proving the stated expected bound and success probability" (p.20)
--   - encoding: a state with reward at least p⋆ − ε → selectorReward Env ρ ≥ p⋆ − ε for the reduced state ρ of the selector register; reason: reward(ρ) of Problem 3.12
--   - encoding: O(·), Ω(·), polylog, Õ → absolute constants C > 0, K ∈ ℕ (and c > 0) chosen before every parameter, polylog(x) = (log x)^K; reason: base mission convention; the bounds are uniform in the instance
--   - encoding: a quantum algorithm with controlled access to the oracle → one OracleAlg of the base mission, fixed before the instance; controlled uses of the oracle and its inverse each count one query; reason: an algorithm chosen after the instance would know the answer; base algorithm model
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 4.4 and its proof, p.20 (PDF p.21); (7), p.17 (PDF p.18); Problem 3.12, p.13 (PDF p.14)

import Definitions.Def_GapAgnosticGS_pStar
import Definitions.Def_GapAgnosticGS_OracleAlg_successProb
import Definitions.Def_GapAgnosticGS_OracleAlg_expQueries
import Definitions.Def_GapAgnosticGS_Supplement_oracleSum
import Definitions.Def_GapAgnosticGS_Supplement_armL
import Definitions.Def_GapAgnosticGS_Supplement_selectorReward
open QAlgorithms

namespace GapAgnosticGS.Supplement

open scoped ENNReal

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 4.4, p.20 (PDF p.21): "Given a HidQMAB instance E and U_I satisfying (7)
with overlap γ > 0, for every ε ∈ (0, 1/8), δ ∈ (0, 1/3), there exists a quantum algorithm that
– prepares a state with reward at least p⋆ − ε with probability at least 1 − δ, – uses
O((1/γ)√L(ε, {p_j}, |ψ_I⟩) polylog(1/(εγδ))) queries to controlled version of E and its inverse and
the same order of queries to controlled versions of U_I and its inverse"; the proof ends
"proving the stated expected bound and success probability" (p.20). (7), p.17 (PDF p.18):
"U_I |0⟩ = |ψ_I⟩ = Σ_j c_j |ϕ_j⟩, ‖Π⋆ |ψ_I⟩‖ ≥ γ"; reward of a state: Problem 3.12, p.13 (PDF p.14).

There are absolute `C > 0`, `K` such that for every `n ≥ 1`, arm register `A` with known `|0⟩_A`
and `Π`, `γ > 0`, `ε ∈ (0, 1/8)` and `δ ∈ (0, 1/3)` one algorithm with output on the selector
register `ℂⁿ`, fixed before the instance, satisfies for every hidden-basis environment `E` (best
arms possibly degenerate) and every unitary `U_I` with `‖Π⋆ U_I|0⟩‖² ≥ γ²`: with probability at
least `1 − δ` it halts with a selector state `ρ` with `reward(ρ) ≥ p⋆ − ε`, and its expected number
of controlled queries to `E ⊕ U_I` is at most `C (1/γ) √L(ε, {p_j}, ψ_I) · log^K(1/(εγδ))`.

**Formalization Note.** Two-oracle access is the direct sum `oracleSum E U_I` (see `oracleSum`).
`reward(ρ)` is `selectorReward Env ρ = Re tr((1 ⊗ Π) E (ρ ⊗ |0⟩⟨0|) E†)` of Problem 3.12, the
reward of the output state, not of a single arm. `‖Π⋆ ψ‖² = Σ_{j : p_j = p⋆} |⟨ϕ_j, ψ⟩|²`. The
"queries" are expected queries (the proof's "stated expected bound"), in `ℝ≥0∞`. -/
theorem theorem_4_4 :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (n : ℕ) [NeZero n], ∀ (A : Type) [Fintype A] [DecidableEq A] (a₀ : A)
        (Prj : Matrix A A ℂ) (γ ε δ : ℝ), 0 < γ → ε ∈ Set.Ioo 0 (1 / 8) →
        δ ∈ Set.Ioo 0 (1 / 3) →
      ∃ alg : OracleAlg ((Fin n × A) ⊕ Fin n) (Fin n) Unit,
        ∀ (Env : HidEnv n A a₀ Prj), ∀ UI ∈ Matrix.unitaryGroup (Fin n) ℂ,
          γ ^ 2 ≤ ∑ j ∈ Finset.univ.filter (fun j => reward Env j = pStar Env),
            ‖inner ℂ (Env.φ j) (act UI (ket (0 : Fin n)))‖ ^ 2 →
          ENNReal.ofReal (1 - δ) ≤ alg.successProb (oracleSum Env.E UI)
              (fun _ ρ => pStar Env - ε ≤ selectorReward Env ρ) ∧
          alg.expQueries (oracleSum Env.E UI) ≤
            ENNReal.ofReal (C * (1 / γ) * Real.sqrt (armL Env ε (act UI (ket (0 : Fin n)))) *
              Real.log (1 / (ε * γ * δ)) ^ K) := by sorry

end GapAgnosticGS.Supplement
