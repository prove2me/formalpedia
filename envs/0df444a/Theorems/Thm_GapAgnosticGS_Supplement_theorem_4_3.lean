-- Prove2me | Theorems.Thm_GapAgnosticGS_Supplement_theorem_4_3
-- name    : GapAgnosticGS.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:32:38.087365+00:00
-- url     : https://prove2.me/theorems/8cd9ff9b-8909-4bc3-b0b0-c8be6821ea3a
-- title:
--   Theorem 4.3 — gap-free best reward estimation from a guided state
-- statement:
--   Let $E$ be a hidden-basis environment with $n\ge1$ arms, hidden basis $\{|\phi_j\rangle\}$, rewards $p_j$ and best reward $p_\star$ (best arms may be degenerate), and let $U_I$ be a unitary on the selector register with $|\psi_I\rangle=U_I|0\rangle$ satisfying the overlap condition (7): $\|\Pi_\star|\psi_I\rangle\|\ge\gamma>0$, where $\Pi_\star$ projects onto the span of all best arms. The learner has controlled access to $E$, $U_I$ and their inverses.
--
--   There are absolute constants $C>0$ and $K$ such that for every $n\ge1$, arm register with known $|0\rangle_A$ and $\Pi$, $\gamma>0$, $h\in(0,1/4)$ and $\delta\in(0,1/3)$ there is one algorithm which, for every such $E$ and $U_I$:
--
--   1. outputs, with probability at least $1-\delta$, a real number $\hat p$ with $|\hat p-p_\star|\le h$;
--   2. makes in expectation at most
--   $$
--   C\,\frac1\gamma\sqrt{L(h,\{p_j\},|\psi_I\rangle)}\,\Big(\log\frac1{\delta\gamma h}\Big)^K
--   $$
--   controlled queries to $E$, $U_I$ and their inverses;
--   3. makes on every run at most $C\,\frac{1}{\gamma h}\big(\log\frac1{\delta\gamma h}\big)^K$ such queries.
--
--   No lower bound on any reward gap is assumed. The instance-dependent bound improves the gap-free ground-energy estimation of Lin and Tong, $\tilde O(1/(\gamma h))$ in these units, whenever the initial state has little weight on arms with rewards close to $p_\star$.
--
--   **Formalization Note** The two oracles are the direct sum `oracleSum Env.E UI`; the output is the classical output of the algorithm (type `ℝ`) and its output register is trivial.
--
--   Differences from the source:
--   - encoding: queries to the first oracle and the same order of queries to the second → queries to the direct sum oracleSum of the two unitaries; reason: one query to the sum is one query to each, and one query to either is one query to the sum, so the two counts agree up to a factor 2
--   - encoding: (7): ‖Π⋆|ψI⟩‖ ≥ γ with Π⋆ = Σ_{j: p_j = p⋆} |ϕ_j⟩⟨ϕ_j| → γ² ≤ Σ_{j: p_j = p⋆} |⟨ϕ_j, U_I|0⟩⟩|² for a unitary U_I on ℂⁿ, γ > 0; reason: ‖Π⋆ψ‖² = Σ_{j: p_j = p⋆} |c_j|² in the hidden orthonormal basis; both sides nonnegative
--   - reading: "Therefore, the worst-case query complexity is Õ(1/(γh))" → maxQueries ≤ C (1/(γh)) · log^K(1/(δγh)) on every instance satisfying (7); reason: the proof supplies a deterministic cap ("Its deterministic cap is Õ(t_max/γ) even when neither promise holds", p.19; "t_max = O(h⁻¹ log(1/a)) even if a previous test returned an incorrect interval", p.20); polylog read with the argument of (9)
--   - encoding: an algorithm that estimates p⋆ with additive error at most h → the halting classical output o : ℝ satisfies |o − p⋆| ≤ h; output register Unit; reason: the estimate is classical
--   - encoding: O(·), Ω(·), polylog, Õ → absolute constants C > 0, K ∈ ℕ (and c > 0) chosen before every parameter, polylog(x) = (log x)^K; reason: base mission convention; the bounds are uniform in the instance
--   - encoding: a quantum algorithm with controlled access to the oracle → one OracleAlg of the base mission, fixed before the instance; controlled uses of the oracle and its inverse each count one query; reason: an algorithm chosen after the instance would know the answer; base algorithm model
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 4.3, p.18 (PDF p.19), with its proof, pp.18–20 (PDF pp.19–21); (7), p.17 (PDF p.18); Definition 4.2, p.18 (PDF p.19)

import Definitions.Def_GapAgnosticGS_pStar
import Definitions.Def_GapAgnosticGS_OracleAlg_successProb
import Definitions.Def_GapAgnosticGS_OracleAlg_expQueries
import Definitions.Def_GapAgnosticGS_OracleAlg_maxQueries
import Definitions.Def_GapAgnosticGS_Supplement_oracleSum
import Definitions.Def_GapAgnosticGS_Supplement_armL
open QAlgorithms

namespace GapAgnosticGS.Supplement

open scoped ENNReal

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 4.3 (Gap-free best reward estimation), p.18 (PDF p.19): "Given a HidQMAB
instance E and U_I satisfying (7) with overlap γ > 0, for every h ∈ (0, 1/4) and δ ∈ (0, 1/3),
there is an algorithm that estimates p⋆ with additive error at most h, with probability at least
1 − δ, and with an expected number of O((1/γ)√L(h, {p_j}, |ψ_I⟩) polylog(1/(δγh))), (9) queries to
controlled version of E and its inverse, and the same order of queries to controlled version of
U_I and its inverse. Therefore, the worst-case query complexity is Õ(1/(γh))"; (7), p.17
(PDF p.18): "U_I |0⟩ = |ψ_I⟩ = Σ_j c_j |ϕ_j⟩, ‖Π⋆ |ψ_I⟩‖ ≥ γ", `Π⋆ := Σ_{j : p_j = p⋆} |ϕ_j⟩⟨ϕ_j|`
("Through this section, we allow degenerate best arms").

There are absolute `C > 0`, `K` such that for every `n ≥ 1`, arm register `A` with known `|0⟩_A`
and `Π`, `γ > 0`, `h ∈ (0, 1/4)` and `δ ∈ (0, 1/3)` one algorithm with classical real output, fixed
before the instance, satisfies for every hidden-basis environment `E` and every unitary `U_I` on
the selector register with `‖Π⋆ U_I|0⟩‖² ≥ γ²`:
1. with probability at least `1 − δ` it halts with an estimate `o` with `|o − p⋆| ≤ h`;
2. its expected number of controlled queries to `E ⊕ U_I` is at most
   `C (1/γ) √L(h, {p_j}, ψ_I) · log^K(1/(δγh))`;
3. on every run it makes at most `C (1/(γh)) · log^K(1/(δγh))` queries.

**Formalization Note.** The two oracles are one `OracleAlg` oracle, the direct sum
`oracleSum E U_I` on `(Fin n × A) ⊕ Fin n` (one query to the sum is one query to each; one query to
either is one query to the sum), so "O(X) queries to E and the same order to U_I" is "O(X) queries
to the sum". `‖Π⋆ ψ‖² = Σ_{j : p_j = p⋆} |⟨ϕ_j, ψ⟩|²` in the hidden basis. The output register is
`Unit` (the output is classical). Clause 3 reads "the worst-case query complexity is Õ(1/(γh))" as
a bound on `maxQueries` on every instance satisfying (7) (the proof's deterministic cap, pp.19–20,
"even if a previous test returned an incorrect interval"). -/
theorem theorem_4_3 :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (n : ℕ) [NeZero n], ∀ (A : Type) [Fintype A] [DecidableEq A] (a₀ : A)
        (Prj : Matrix A A ℂ) (γ h δ : ℝ), 0 < γ → h ∈ Set.Ioo 0 (1 / 4) →
        δ ∈ Set.Ioo 0 (1 / 3) →
      ∃ alg : OracleAlg ((Fin n × A) ⊕ Fin n) Unit ℝ,
        ∀ (Env : HidEnv n A a₀ Prj), ∀ UI ∈ Matrix.unitaryGroup (Fin n) ℂ,
          γ ^ 2 ≤ ∑ j ∈ Finset.univ.filter (fun j => reward Env j = pStar Env),
            ‖inner ℂ (Env.φ j) (act UI (ket (0 : Fin n)))‖ ^ 2 →
          ENNReal.ofReal (1 - δ) ≤ alg.successProb (oracleSum Env.E UI)
              (fun o _ => |o - pStar Env| ≤ h) ∧
          alg.expQueries (oracleSum Env.E UI) ≤
            ENNReal.ofReal (C * (1 / γ) * Real.sqrt (armL Env h (act UI (ket (0 : Fin n)))) *
              Real.log (1 / (δ * γ * h)) ^ K) ∧
          ((alg.maxQueries (oracleSum Env.E UI) : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal (C * (1 / (γ * h)) * Real.log (1 / (δ * γ * h)) ^ K) := by sorry

end GapAgnosticGS.Supplement
