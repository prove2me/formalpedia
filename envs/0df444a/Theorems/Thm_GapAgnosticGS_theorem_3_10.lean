-- Prove2me | Theorems.Thm_GapAgnosticGS_theorem_3_10
-- name    : GapAgnosticGS.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:27.295612+00:00
-- url     : https://prove2.me/theorems/5afe1d93-3641-4eb9-a495-ab51cfe40051
-- title:
--   Theorem 3.10 — best-arm state preparation in a hidden basis with $O(\sqrt\Gamma\,\mathrm{polylog})$ expected queries
-- statement:
--   There are absolute constants $C>0$ and $K\in\mathbb N$ with the following property. Let $n\ge2$, let $A$ be an arm register with known $|0\rangle_A$ and reward projector $\Pi$, and let $\epsilon,\delta>0$. There is one algorithm, built without knowledge of the environment and using controlled queries to $E$ and $E^\dagger$, such that for every hidden-basis environment $E$ with $\Delta_{\rm arm}>0$ (unique best arm $j_\star$):
--
--   1. with probability at least $1-\delta$ it outputs a state $\rho_I$ on the selector register with
--   $$\mathrm{tr}\big(\rho_I|\phi_{j_\star}\rangle\langle\phi_{j_\star}|\big)\ge1-\epsilon ;$$
--   2. its expected number of queries is at most $C\sqrt\Gamma\log^K\frac{n}{\delta\epsilon\Delta_{\rm arm}}$.
--
--   This solves Problem 3.2 (hidden-basis best-arm identification) with the same leading gap dependence as the known-basis quantum algorithm of Wang–You–Li–Childs.
--
--   Differences from the source:
--   - reading: For any environment E … there exists a quantum algorithm → one algorithm chosen before E (after n, A, |0⟩_A, Π, ϵ, δ); reason: an algorithm allowed to depend on E would know ϕ_{j⋆}; App. A.7 builds one algorithm for all environments
--   - reading: O/polylog → absolute C and K chosen before every other quantity; polylog(x) = (log x)^K; reason: the standard meaning
--   - encoding: output a state ρ_I on the input register I; tr(ρ_I |ϕ_{j*}⟩⟨ϕ_{j*}|); j* = arg max p_j → the reduced output state ρ of the output register ℂⁿ (arm register, control and workspace traced out); ⟨ϕ_j|ρ|ϕ_j⟩ for the j with p_j = p⋆; reason: the same quantities; the maximizer is unique when armGap > 0
--   - encoding: n arms (range unstated in the statement) → 2 ≤ n; reason: the paper's standing setting (p.2: 'an n-dimensional Hilbert space, where n ≥ 2'), and p_2 and ∆_arm = p⋆ − max_{j≠j⋆} p_j need a second arm; excludes only the case where these are undefined
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 3.10, p.13 (PDF p.14); Problem 3.2, p.9 (PDF p.10); proof in App. A.7, pp.34–35 (PDF pp.35–36)

import Definitions.Def_GapAgnosticGS_HidEnv
import Definitions.Def_GapAgnosticGS_pStar
import Definitions.Def_GapAgnosticGS_armGap
import Definitions.Def_GapAgnosticGS_armComplexity
import Definitions.Def_GapAgnosticGS_OracleAlg_successProb
import Definitions.Def_GapAgnosticGS_OracleAlg_expQueries
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 3.10, p.13 (PDF p.14): "For any environment E, as in Definition 1.4, with n arms
and non-zero ∆_arm > 0, there exists a quantum algorithm that, given controlled access to E and
E†, solves the best arm identification in Problem 3.2 using O(√Γ polylog(n/(δϵ∆_arm))) expected
queries"; Problem 3.2, p.9 (PDF p.10): "Given ϵ, δ > 0, and controlled access to a HidQMAB
environment E … and its inverse E†, with probability at least 1 − δ, output a state ρ_I on the
input register I such that tr(ρ_I |ϕ_{j∗}⟩⟨ϕ_{j∗}|) ≥ 1 − ϵ, where j∗ = arg max_j p_j. The query
complexity of an algorithm is the number of controlled queries to E and E†."

There are absolute `C`, `K` such that for every `n ≥ 2`, arm register with known `|0⟩_A` and `Π`,
and `ϵ, δ > 0`, one algorithm with output register `I = ℂⁿ`, fixed before the environment,
satisfies for every environment with `∆_arm > 0`: with probability at least `1 − δ` it halts with
an output state `ρ` with `⟨ϕ_{j⋆}|ρ|ϕ_{j⋆}⟩ ≥ 1 − ϵ`, and its expected number of queries is at most
`C √Γ log^K(n/(δϵ∆_arm))`.

**Formalization Note.** The algorithm is chosen before the environment (the paper builds one
algorithm in App. A.7; an algorithm allowed to depend on `E` would know `ϕ_{j⋆}`). `ρ` is the
reduced state of the output register, the arm register, controls and workspace traced out.
`j⋆` is the unique `j` with `p_j = p⋆`. O(·)/polylog are absolute constants. -/
theorem theorem_3_10 :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ (A : Type) [Fintype A] [DecidableEq A] (a₀ : A) (Prj : Matrix A A ℂ)
      (ϵ δ : ℝ), 0 < ϵ → 0 < δ →
    ∃ alg : OracleAlg (Fin n × A) (Fin n) Unit,
      ∀ Env : HidEnv n A a₀ Prj, 0 < armGap Env →
        ENNReal.ofReal (1 - δ) ≤ alg.successProb Env.E (fun _ ρ =>
          ∀ j, reward Env j = pStar Env → 1 - ϵ ≤ (inner ℂ (Env.φ j) (act ρ (Env.φ j))).re) ∧
        alg.expQueries Env.E ≤ ENNReal.ofReal
          (C * Real.sqrt (armComplexity Env) * Real.log (n / (δ * ϵ * armGap Env)) ^ K) := by sorry

end GapAgnosticGS
