-- Prove2me | Theorems.Thm_GapAgnosticGS_Supplement_theorem_1_2
-- name    : GapAgnosticGS.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:30:49.388198+00:00
-- url     : https://prove2.me/theorems/cd45b500-dcbe-4a06-9e81-1f6d1b2ed41e
-- title:
--   Theorem 1.2 — PAC ground energy without uniqueness: $\tilde O(\alpha\sqrt n/\varepsilon)$ worst-case queries, tight for some families
-- statement:
--   Let $H$ be a Hermitian matrix on $\mathbb C^n$, $n\ge2$, with all eigenvalues in $[-\alpha,\alpha]$ and ground energy $E_0$; the ground space may be degenerate and no gap is assumed. The learner has controlled access to the phase oracle $W_H=e^{i\pi H/(4\alpha)}$ and its inverse, each use counting one query. A state $\rho$ has **expected energy** $\operatorname{tr}(H\rho)$.
--
--   1. **Upper bound.** There are absolute constants $C>0$ and $K$ such that for every $n\ge2$, $\alpha>0$, $\varepsilon>0$ and $\delta\in(0,1/3)$ there is one algorithm which, for every such $H$, outputs with probability at least $1-\delta$ a state $\rho$ with $\operatorname{tr}(H\rho)\le E_0+\varepsilon$, and on every run makes at most
--   $$
--   C\,\frac{\alpha\sqrt n}{\varepsilon}\,\Big(\log\frac{n\alpha}{\delta\varepsilon}\Big)^K
--   $$
--   queries.
--   2. **Lower bound.** There is an absolute constant $c>0$ such that for every $n\ge4$, $\alpha>0$ and $0<\varepsilon<\alpha/4$ there is a nonempty family of Hermitian matrices with eigenvalues in $[-\alpha,\alpha]$ such that every algorithm that, on each member, outputs with probability at least $2/3$ a state of expected energy at most $E_0+\varepsilon$ makes at least
--   $$
--   c\,\frac{\alpha\sqrt n}{\varepsilon}
--   $$
--   queries in the worst case on some member.
--
--   This is the probably-approximately-correct counterpart of ground-state preparation: when the gap is tiny or the ground space degenerate, the goal of approaching one ground state is replaced by reaching energy within $\varepsilon$ of $E_0$, and the cost is then governed by $\sqrt n/\varepsilon$ with no spectral parameter, which is optimal.
--
--   **Formalization Note** Algorithms are the base mission's adaptive `OracleAlg (Fin n) (Fin n) Unit`; $\rho$ is the reduced state of the output register. "Using … queries" in the upper bound is the worst-case count `maxQueries` (in $\mathbb N_\infty$, compared in $\mathbb R_{\ge0}^\infty$), which also bounds the expected count of Corollary 3.13.
--
--   Differences from the source:
--   - reading: "with high probability" (abbreviated statement) → probability at least 1 − δ for every δ ∈ (0, 1/3), δ entering the polylog; reason: Corollary 3.13 and its proof (App. A.8), from which the upper bound is drawn
--   - reading: "using O(α√n/ε polylog(nα/(δε))) queries" → worst-case count maxQueries ≤ C α√n/ε · log^K(nα/(δε)) on every run; reason: App. A.8: "The deterministic cap in Lemma A.6 is therefore O((√n/ε) polylog(n/(δε))) even if the interval is incorrect"; the worst-case bound implies the expected bound of Corollary 3.13
--   - reading: "any algorithm preparing a state of expected energy at most E0 + ε requires Ω(α√n/ε) queries" → every algorithm succeeding with probability ≥ 2/3 on each member of a nonempty family F makes ≥ c α√n/ε worst-case queries on some member of F; reason: the success probability 2/3 and the worst-case reading are those of Corollary 3.17 and of the proof of Theorem 3.15 it invokes
--   - encoding: ‖H‖ ≤ α → H Hermitian with every eigenvalue |E_j| ≤ α; reason: the spectral norm of a Hermitian matrix is its largest eigenvalue modulus (p.1: spec(H) ⊆ [−α, α]); base convention
--   - encoding: expected energy of ρ; E0 → Re tr(Hρ) of the reduced output state; E0 = minEigenvalue H; reason: tr(Hρ) is real for a density matrix; base output-state convention
--   - encoding: O(·), Ω(·), polylog, Õ → absolute constants C > 0, K ∈ ℕ (and c > 0) chosen before every parameter, polylog(x) = (log x)^K; reason: base mission convention; the bounds are uniform in the instance
--   - encoding: a quantum algorithm with controlled access to the oracle → one OracleAlg of the base mission, fixed before the instance; controlled uses of the oracle and its inverse each count one query; reason: an algorithm chosen after the instance would know the answer; base algorithm model
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.2 (abbreviated), p.3 (PDF p.4); Corollary 3.13, p.13 (PDF p.14) and App. A.8, pp.35–36 (PDF pp.36–37); Corollary 3.17, p.17 (PDF p.18)

import Definitions.Def_GapAgnosticGS_phaseOracle
import Definitions.Def_GapAgnosticGS_energy
import Definitions.Def_GapAgnosticGS_OracleAlg_successProb
import Definitions.Def_GapAgnosticGS_OracleAlg_maxQueries
open QAlgorithms

namespace GapAgnosticGS.Supplement

open scoped ENNReal

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.2 (abbreviated), p.3 (PDF p.4): "For any H, ‖H‖ ≤ α with possibly non-unique
ground states, there exists a quantum algorithm that, with high probability, outputs a state with
expected energy at most E_0 + ε using O(α√n/ε polylog(nα/(δε))) = Õ(α√n/ε) queries. Moreover,
for any n ≥ 4, α > 0, and 0 < ε < α/4, there is a family of Hamiltonians with ‖H‖ ≤ α such that
any algorithm preparing a state of expected energy at most E_0 + ε requires Ω(α√n/ε) queries."
Unabbreviated forms: Corollary 3.13, p.13 (PDF p.14) and its proof, App. A.8, pp.35–36
(PDF pp.36–37) ("with probability at least 1 − δ"; "The deterministic cap in Lemma A.6 is
therefore O((√n/ε) polylog(n/(δε))) even if the interval is incorrect"); Corollary 3.17, p.17
(PDF p.18) ("preparing, with probability at least 2/3, a state whose expected energy is at most
E_0 + ε … requires Ω(α√n/ε) controlled queries to W_H and its inverse").

(a) **Upper bound.** There are absolute `C > 0`, `K` such that for every `n ≥ 2`, `α > 0`,
`ε > 0` and `δ ∈ (0, 1/3)` one algorithm, fixed before `H`, satisfies for every Hermitian `H` on
`ℂⁿ` with all eigenvalues in `[−α, α]` (no uniqueness or gap promise): with probability at least
`1 − δ` it halts with an output state `ρ` with `Re tr(Hρ) ≤ E_0 + ε`, and on every run it makes at
most `C α √n / ε · log^K(nα/(δε))` queries to `W_H`, `τ = π/(4α)`.

(b) **Lower bound.** There is an absolute `c > 0` such that for every `n ≥ 4`, `α > 0` and
`0 < ε < α/4` there is a nonempty family of Hermitian matrices with eigenvalues in `[−α, α]` such
that every algorithm that, for each member, outputs with probability at least `2/3` a state of
expected energy at most `E_0 + ε` makes at least `c α √n / ε` queries in the worst case on some
member.

**Formalization Note.** Algorithms are the base mission's `OracleAlg (Fin n) (Fin n) Unit`
(adaptive, mid-run measurements, no depth bound, controlled `W_H`/`W_H†` queries each counted
once); `ρ` is the reduced state of the output register `ℂⁿ`. "‖H‖ ≤ α" is `|E_j| ≤ α` for every
eigenvalue; `E_0` is `minEigenvalue H`; the expected energy is `Re tr(Hρ)`. "Using … queries" in
(a) is the worst-case count `maxQueries` (`ℕ∞`, compared in `ℝ≥0∞`), which also bounds the
expected count of Corollary 3.13. O/Ω/polylog are absolute constants, `polylog x = (log x)^K`. -/
theorem theorem_1_2 :
    (∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ (α ε δ : ℝ), 0 < α → 0 < ε → δ ∈ Set.Ioo 0 (1 / 3) →
      ∃ A : OracleAlg (Fin n) (Fin n) Unit,
        ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → (∀ j, |energy H j| ≤ α) →
          ENNReal.ofReal (1 - δ) ≤ A.successProb (phaseOracle H α)
              (fun _ ρ => (Matrix.trace (H * ρ)).re ≤ minEigenvalue H + ε) ∧
          ((A.maxQueries (phaseOracle H α) : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal (C * α * Real.sqrt n / ε * Real.log (n * α / (δ * ε)) ^ K)) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 4 ≤ n → ∀ (α ε : ℝ), 0 < α → 0 < ε → ε < α / 4 →
      ∃ F : Set (Matrix (Fin n) (Fin n) ℂ), F.Nonempty ∧
        (∀ H ∈ F, H.IsHermitian ∧ ∀ j, |energy H j| ≤ α) ∧
        ∀ A : OracleAlg (Fin n) (Fin n) Unit,
          (∀ H ∈ F, ENNReal.ofReal (2 / 3) ≤ A.successProb (phaseOracle H α)
              (fun _ ρ => (Matrix.trace (H * ρ)).re ≤ minEigenvalue H + ε)) →
          ∃ H ∈ F, ENNReal.ofReal (c * α * Real.sqrt n / ε) ≤
            ((A.maxQueries (phaseOracle H α) : ℕ∞) : ℝ≥0∞)) := by sorry

end GapAgnosticGS.Supplement
