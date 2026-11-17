-- Prove2me | Theorems.Thm_GapAgnosticGS_Supplement_theorem_1_3
-- name    : GapAgnosticGS.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:31:37.949338+00:00
-- url     : https://prove2.me/theorems/b1e0c5ba-8c98-41ab-a6c0-5ccafcef24af
-- title:
--   Theorem 1.3 — warm start without a gap bound: energy within $\varepsilon$ of $E_0$ with $\tilde O((\alpha/\gamma)\sqrt{L_H(\varepsilon,|\psi_0\rangle)})$ expected queries
-- statement:
--   Let $H$ be a Hermitian matrix on $\mathbb C^n$, $n\ge2$, with all eigenvalues in $[-\alpha,\alpha]$, ground energy $E_0$ and a possibly degenerate ground space, with no known gap bound. The learner has controlled access to $W_H=e^{i\pi H/(4\alpha)}$ and to a unitary $U_0$ preparing $|\psi_0\rangle=U_0|0\rangle$, and to their inverses, and $|\psi_0\rangle$ has overlap amplitude at least $\gamma\in(0,1]$ with the ground space: $\|\Pi_{\mathrm{ground}}|\psi_0\rangle\|\ge\gamma$. Let $L_H(\varepsilon,|\psi_0\rangle)$ be the warm-start complexity.
--
--   There are absolute constants $C>0$ and $K$ such that for every $n\ge2$, $\alpha>0$, $\gamma\in(0,1]$, $\varepsilon>0$ and $\delta\in(0,1/3)$ there is one algorithm which, for every such $H$ and $U_0$, outputs with probability at least $1-\delta$ a state $\rho$ with $\operatorname{tr}(H\rho)\le E_0+\varepsilon$, using in expectation at most
--
--   $$
--   C\,\frac{\alpha}{\gamma}\,\sqrt{L_H(\varepsilon,|\psi_0\rangle)}\;\Big(\log\frac{\alpha}{\varepsilon\gamma\delta}\Big)^K
--   $$
--
--   controlled queries to $W_H$, $U_0$ and their inverses.
--
--   Since $L_H(\varepsilon,|\psi_0\rangle)\le\varepsilon^{-2}$ this is never worse than the guided-state benchmark $\tilde O(\alpha/(\gamma\varepsilon))$, and it is much smaller when the initial state puts little weight on low-lying excitations.
--
--   **Formalization Note** The two oracles are one oracle, the direct sum `oracleSum (phaseOracle H α) U₀`. The ground-space overlap is written as the existence of a unit ground vector $\phi$ with $|\langle\phi,\psi_0\rangle|\ge\gamma$, which is equivalent because $\|\Pi_{\mathrm{ground}}\psi_0\|=\max_\phi|\langle\phi,\psi_0\rangle|$ over unit ground vectors.
--
--   Differences from the source:
--   - reading: ε: "for an accuracy ε > 0" (p.3); ε ∈ (0, 2α) in Corollary 4.6(1) → every ε > 0; reason: p.3 defines L_H for every ε > 0; for ε ≥ 2α every state satisfies tr(Hρ) ≤ E0 + ε, so the larger range adds only trivial cases
--   - reading: "prepares a state … using Õ((α/γ)√L_H(ε, |ψ0⟩)) queries" (abbreviated) → with probability ≥ 1 − δ, expected queries ≤ C (α/γ) √L_H(ε, ψ0) · log^K(α/(εγδ)); reason: Corollary 4.6(1) ("with high probability", "expected queries"), proved from Theorem 4.4 at reward tolerance ε/(32α), whose polylog is polylog(1/(εγδ))
--   - encoding: ground-state overlap ≥ γ (overlap amplitude with the ground space) → ∃ unit ground vector φ with γ ≤ |⟨φ, U0|0⟩⟩|, and γ ∈ (0, 1]; reason: ‖Π_ground ψ0‖ is the maximum of |⟨φ, ψ0⟩| over unit ground vectors; an overlap amplitude is at most 1
--   - encoding: coherent access to a unitary preparing |ψ0⟩ → a unitary U0 on ℂⁿ with ψ0 = U0|0⟩, |0⟩ the basis vector 0; reason: the paper writes U|0⟩ = |ψ⟩ on the system register (p.17, (7))
--   - encoding: queries to the first oracle and the same order of queries to the second → queries to the direct sum oracleSum of the two unitaries; reason: one query to the sum is one query to each, and one query to either is one query to the sum, so the two counts agree up to a factor 2
--   - encoding: ‖H‖ ≤ α → H Hermitian with every eigenvalue |E_j| ≤ α; reason: the spectral norm of a Hermitian matrix is its largest eigenvalue modulus (p.1: spec(H) ⊆ [−α, α]); base convention
--   - encoding: expected energy of ρ; E0 → Re tr(Hρ) of the reduced output state; E0 = minEigenvalue H; reason: tr(Hρ) is real for a density matrix
--   - encoding: O(·), Ω(·), polylog, Õ → absolute constants C > 0, K ∈ ℕ (and c > 0) chosen before every parameter, polylog(x) = (log x)^K; reason: base mission convention; the bounds are uniform in the instance
--   - encoding: a quantum algorithm with controlled access to the oracle → one OracleAlg of the base mission, fixed before the instance; controlled uses of the oracle and its inverse each count one query; reason: an algorithm chosen after the instance would know the answer; base algorithm model
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.3 (abbreviated), p.3 (PDF p.4); Corollary 4.6(1) and its proof, p.21 (PDF p.22)

import Definitions.Def_GapAgnosticGS_phaseOracle
import Definitions.Def_GapAgnosticGS_energy
import Definitions.Def_GapAgnosticGS_OracleAlg_successProb
import Definitions.Def_GapAgnosticGS_OracleAlg_expQueries
import Definitions.Def_GapAgnosticGS_Supplement_oracleSum
import Definitions.Def_GapAgnosticGS_Supplement_LH
open QAlgorithms

namespace GapAgnosticGS.Supplement

open scoped ENNReal

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.3 (abbreviated), p.3 (PDF p.4): "For any H, ‖H‖ ≤ α, there exists a quantum
algorithm that, given access to an initial state |ψ_0⟩ with ground-state overlap ≥ γ, prepares a
state with expected energy at most E_0 + ε using Õ((α/γ)√L_H(ε, |ψ_0⟩)) queries"; setting, p.3:
"we have coherent access to a unitary preparing |ψ_0⟩ = Σ_j c_j |ϕ_j⟩, whose overlap amplitude with
the ground space is at least γ. We assume no known bound on the spectral gap, and the ground space
may be degenerate. For an accuracy ε > 0, define L_H(ε, |ψ_0⟩)". Unabbreviated form: Corollary
4.6(1), p.21 (PDF p.22) ("tr(Hρ) ≤ E_0 + ε with high probability, and Õ((α/γ)√L_H(ε, |ψ_0⟩))
expected queries"), proved from Theorem 4.4 at reward tolerance `ε/(32α)` via Lemma 3.1.

There are absolute `C > 0`, `K` such that for every `n ≥ 2`, `α > 0`, `γ ∈ (0, 1]`, `ε > 0` and
`δ ∈ (0, 1/3)` one algorithm, fixed before `H` and `U_0`, satisfies for every Hermitian `H` on `ℂⁿ`
with all eigenvalues in `[−α, α]` and every unitary `U_0` on `ℂⁿ` whose state `ψ_0 = U_0|0⟩` has
overlap at least `γ` with some unit ground vector (equivalently, `‖Π_ground ψ_0‖ ≥ γ`): with
probability at least `1 − δ` it halts with `ρ` with `Re tr(Hρ) ≤ E_0 + ε`, using in expectation at
most `C (α/γ) √L_H(ε, ψ_0) · log^K(α/(εγδ))` controlled queries to `W_H ⊕ U_0` (that is, to
`W_H`, `U_0` and their inverses).

**Formalization Note.** The two oracles are one `OracleAlg` oracle, the direct sum
`oracleSum W_H U_0` on `Fin n ⊕ Fin n` (one query to the sum is one query to each; one query to
either is one query to the sum). `|0⟩` is the basis vector `0` of `ℂⁿ`. The overlap with the
(possibly degenerate) ground space is `max_{φ ground, ‖φ‖ = 1} |⟨φ, ψ_0⟩| = ‖Π_ground ψ_0‖`, written
as the existence of a unit ground vector `φ` with `γ ≤ |⟨φ, ψ_0⟩|`. Expected counts are in `ℝ≥0∞`.
The polylog argument `α/(εγδ)` is the one the proof gives (no `n`). -/
theorem theorem_1_3 :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ (α γ ε δ : ℝ), 0 < α → γ ∈ Set.Ioc 0 1 → 0 < ε →
        δ ∈ Set.Ioo 0 (1 / 3) →
      ∃ A : OracleAlg (Fin n ⊕ Fin n) (Fin n) Unit,
        ∀ (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), (∀ j, |energy H j| ≤ α) →
        ∀ U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ,
          (∃ φ : EuclideanSpace ℂ (Fin n), IsGroundState H φ ∧
            γ ≤ ‖inner ℂ φ (act U₀ (ket (0 : Fin n)))‖) →
          ENNReal.ofReal (1 - δ) ≤ A.successProb (oracleSum (phaseOracle H α) U₀)
              (fun _ ρ => (Matrix.trace (H * ρ)).re ≤ minEigenvalue H + ε) ∧
          A.expQueries (oracleSum (phaseOracle H α) U₀) ≤
            ENNReal.ofReal (C * (α / γ) * Real.sqrt (LH hH ε (act U₀ (ket (0 : Fin n)))) *
              Real.log (α / (ε * γ * δ)) ^ K) := by sorry

end GapAgnosticGS.Supplement
