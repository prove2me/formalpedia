-- Prove2me | Theorems.Thm_GapAgnosticGS_Supplement_theorem_5_1
-- name    : GapAgnosticGS.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:34:20.679796+00:00
-- url     : https://prove2.me/theorems/610eff0c-1613-4021-aaf2-00ce7767fac3
-- title:
--   Theorem 5.1 — phase-profile stationary-state preparation for ergodic lazy reversible chains
-- statement:
--   Let $P$ be the transition matrix of an ergodic (irreducible and aperiodic), lazy ($P_{xx}\ge1/2$ for every $x$), reversible Markov chain on $n\ge2$ states with stationary distribution $\pi$ in detailed balance with $P$. Its eigenvalues are $1=\lambda_1>\lambda_2\ge\cdots\ge\lambda_n\ge0$; set $\theta_j=\arccos\lambda_j$ for $j=2,\dots,n$. The learner has controlled access to a transition oracle $O_P$, any unitary with $O_P|x\rangle|0\rangle=|x\rangle\sum_y\sqrt{P_{xy}}\,|y\rangle$, and its inverse, and is given $\underline\theta$ with $0<\underline\theta\le\theta_2$. Write $S=\sum_{j=2}^n\theta_j^{-2}$ and $|\sqrt\pi\rangle=\sum_x\sqrt{\pi_x}|x\rangle$.
--
--   There are absolute constants $C>0$ and $K$ such that for every $n\ge2$, $\underline\theta>0$ and $\delta,\epsilon\in(0,1/3)$ there is one algorithm which, for every such chain and oracle:
--
--   1. outputs with probability at least $1-\delta$ a state within trace distance $\epsilon$ of $|\sqrt\pi\rangle\langle\sqrt\pi|$;
--   2. makes in expectation at most
--   $$
--   C\Big[\frac1{\underline\theta^2}+\sum_{j=2}^n\frac1{\theta_j^2}\Big]^{1/2}\Big(\log\frac{n}{\delta\epsilon\underline\theta}\Big)^K
--   $$
--   calls to $O_P$ and $O_P^\dagger$;
--   3. if $\theta_2\le\kappa\underline\theta$ for some $\kappa\ge1$ (the case $\underline\theta=\Theta(\theta_2)$), makes in expectation at most $C\kappa\sqrt S\,(\log\frac{n}{\delta\epsilon\underline\theta})^K$ calls;
--   4. moreover $S\le\frac12\sum_{j=2}^n\frac1{1-\lambda_j}$, and under the same condition the expected number of calls is at most $C\kappa\big(\frac12\sum_{j=2}^n\frac1{1-\lambda_j}\big)^{1/2}(\log\frac{n}{\delta\epsilon\underline\theta})^K$.
--
--   Measuring the output gives a sample within total variation distance $\epsilon$ of $\pi$. The bound depends on the whole phase profile of the walk rather than only on the spectral gap $1-\lambda_2$.
--
--   **Formalization Note** The eigenvalues are those of the discriminant $D=\mathrm{diag}(\sqrt\pi)\,P\,\mathrm{diag}(\sqrt\pi)^{-1}$, which is symmetric by detailed balance and similar to $P$, sorted decreasingly with 0-based indices. Ergodicity, stationarity and detailed balance are the published `mm_basic` notions; laziness is the paper's $P_{xx}\ge1/2$.
--
--   Differences from the source:
--   - encoding: the eigenvalues λ_1 ≥ … ≥ λ_n of P → descEigenvalues of the discriminant D = diag(√π) P diag(√π)⁻¹, 0-based; reason: D is similar to P and Hermitian by detailed balance (the paper uses D on p.23), so they have the same eigenvalues and D gives a well-defined sorted real list
--   - encoding: ergodic, lazy, reversible chain with stationary distribution π → IsStochastic P, Irreducible P, Aperiodic P, P_xx ≥ 1/2 for all x, IsStationary P π, DetailedBalance P π; reason: ergodic = irreducible and aperiodic; laziness is the paper's convention "P_xx ≥ 1/2" (p.22), not the lazy chain (I + P)/2
--   - encoding: a lower bound 0 < θ̲ ≤ θ_2 → 0 < θ̲ and θ̲ ≤ θ_j for every j ≥ 2; reason: θ_2 is the smallest θ_j since arccos is decreasing
--   - encoding: controlled access to the transition oracle O_P and its inverse → the algorithm succeeds for every unitary O_P on ℂⁿ ⊗ ℂⁿ with O_P|x⟩|0⟩ = |x⟩Σ_y √P_xy|y⟩; controlled O_P and O_P† uses are its queries; reason: the paper specifies O_P only through this action
--   - encoding: a state within trace distance ϵ of |√π⟩ → traceDist(ρ, |√π⟩⟨√π|) ≤ ϵ with traceDist = ½‖·‖₁, ρ the reduced output state; reason: standard trace distance (published ClonableQMASep.Main.traceDist)
--   - reading: "If θ̲ = Θ(θ_2), this simplifies to Õ(√(Σ_j 1/arccos²(λ_j)))" → for every κ ≥ 1 with θ_2 ≤ κθ̲: expected queries ≤ C κ √S · log^K(n/(δϵθ̲)); reason: Θ(θ_2) with an explicit constant κ (the lower bound θ̲ ≤ θ_2 is already assumed); Õ hides the same polylog as the main bound
--   - reading: "≤ Õ(√((1/2) Σ_j 1/(1 − λ_j)))" in (20) → S ≤ ½ Σ_{j≥2} 1/(1 − λ_j), and the bound of the previous line with √(½ Σ 1/(1 − λ_j)); reason: the display asserts both the inequality between the two sums and the resulting bound
--   - encoding: O(·), Ω(·), polylog, Õ → absolute constants C > 0, K ∈ ℕ (and c > 0) chosen before every parameter, polylog(x) = (log x)^K; reason: base mission convention; the bounds are uniform in the instance
--   - encoding: a quantum algorithm with controlled access to the oracle → one OracleAlg of the base mission, fixed before the instance; controlled uses of the oracle and its inverse each count one query; reason: an algorithm chosen after the instance would know the answer; base algorithm model
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 5.1 and Eq. (20), p.23 (PDF p.24); §5, p.22 (PDF p.23)

import Definitions.Def_GapAgnosticGS_OracleAlg_successProb
import Definitions.Def_GapAgnosticGS_OracleAlg_expQueries
import Definitions.Def_GapAgnosticGS_Supplement_descEigenvalues
import Definitions.Def_mm_basic
import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant
import Definitions.Def_ClonableQMASep_Main_Channels
open QAlgorithms MarkovMixing QuantumWalkSearch.SingularGap ClonableQMASep.Main

namespace GapAgnosticGS.Supplement

open scoped ENNReal

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 5.1 (Phase-profile stationary-state preparation), p.23 (PDF p.24): "Let P be the
transition matrix of an ergodic, lazy, reversible Markov chain on n ≥ 2 states with stationary
distribution π. Write its eigenvalues as 1 = λ_1 > λ_2 ≥ ⋯ ≥ λ_n ≥ 0, and set θ_j := arccos(λ_j)
for j = 2, …, n. Suppose we have controlled access to the transition oracle
O_P |x⟩|0⟩ = |x⟩ Σ_y √P_xy |y⟩ and its inverse O_P†, and are given a lower bound 0 < θ̲ ≤ θ_2. For
any δ, ϵ ∈ (0, 1/3), there is an algorithm that, with probability at least 1 − δ, prepares a state
within trace distance ϵ of |√π⟩ := Σ_x √π_x |x⟩. The expected number of calls to O_P and O_P† is
O([1/θ̲² + Σ_{j=2}^n 1/θ_j²]^{1/2} polylog(n/(δϵθ̲))) transition oracle queries. If θ̲ = Θ(θ_2), this
simplifies to Õ(√(Σ_{j=2}^n 1/arccos²(λ_j))) ≤ Õ(√((1/2) Σ_{j=2}^n 1/(1 − λ_j))). (20)"; §5,
p.22 (PDF p.23): "We use the convention P_xx ≥ 1/2 for laziness".

There are absolute `C > 0`, `K` such that for every `n ≥ 2`, `θ̲ > 0` and `δ, ϵ ∈ (0, 1/3)` one
algorithm, fixed before the chain, satisfies for every row-stochastic, irreducible, aperiodic
`P` on `n` states with `P_xx ≥ 1/2` for all `x`, stationary distribution `π` in detailed balance
with `P`, with `θ̲ ≤ θ_j` for all `j ≥ 2`, and for every unitary `O_P` on `ℂⁿ ⊗ ℂⁿ` with
`O_P|x⟩|0⟩ = |x⟩ Σ_y √P_xy |y⟩`, writing `S = Σ_{j ≥ 2} 1/θ_j²`:
1. with probability at least `1 − δ` it halts with `ρ` within trace distance `ϵ` of `|√π⟩⟨√π|`;
2. its expected number of queries is at most `C √(1/θ̲² + S) · log^K(n/(δϵθ̲))`;
3. (θ̲ = Θ(θ_2)) for every `κ ≥ 1` with `θ_2 ≤ κ θ̲`, it is at most `C κ √S · log^K(n/(δϵθ̲))`;
4. `S ≤ (1/2) Σ_{j ≥ 2} 1/(1 − λ_j)`, and for every `κ ≥ 1` with `θ_2 ≤ κ θ̲` the expected number
   of queries is at most `C κ √((1/2) Σ_{j≥2} 1/(1 − λ_j)) · log^K(n/(δϵθ̲))`.

**Formalization Note.** Ergodic is irreducible and aperiodic (`mm_basic`); lazy is the paper's
`P_xx ≥ 1/2`, not `mm_basic.lazy`. The eigenvalues `λ_1 ≥ ⋯ ≥ λ_n` are those of the discriminant
`D = diag(√π) P diag(√π)^{−1}` (`QuantumWalkSearch.SingularGap.discriminant`), which is Hermitian by
detailed balance and similar to `P`; `λ_j` is `descEigenvalues D (j − 1)` (0-based), so "j ≥ 2" is
`1 ≤ j`. `θ̲ ≤ θ_2` is `θ̲ ≤ θ_j` for all `j ≥ 2` (`θ_2` is the smallest of them), and `θ_2 ≤ κθ̲` is
"some `θ_j`, `j ≥ 2`, is `≤ κθ̲`". `|0⟩` is the basis state `0`; the algorithm must work for every
unitary with the stated action (the paper fixes only that). Queries are the `OracleAlg`
controlled `O_P`/`O_P†` queries; the output register is the first register. "θ̲ = Θ(θ_2)" is read
with an explicit linear dependence on the constant `κ`. -/
theorem theorem_5_1 :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ (θl δ ϵ : ℝ), 0 < θl → δ ∈ Set.Ioo 0 (1 / 3) →
        ϵ ∈ Set.Ioo 0 (1 / 3) →
      ∃ alg : OracleAlg (Fin n × Fin n) (Fin n) Unit,
        ∀ (P : Matrix (Fin n) (Fin n) ℝ) (π : Fin n → ℝ),
          IsStochastic P → MarkovMixing.Irreducible P → Aperiodic P → (∀ x, 1 / 2 ≤ P x x) →
          IsStationary P π → DetailedBalance P π →
          (∀ j : Fin n, 1 ≤ (j : ℕ) →
            θl ≤ Real.arccos (descEigenvalues (discriminant P π) j)) →
        ∀ OP ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ,
          (∀ x : Fin n, act OP (ket (x, (0 : Fin n))) =
            tensorVec (ket x) (WithLp.toLp 2 fun y => ((Real.sqrt (P x y) : ℝ) : ℂ))) →
          let lam := descEigenvalues (discriminant P π)
          let S := ∑ j ∈ Finset.univ.filter (fun j : Fin n => 1 ≤ (j : ℕ)),
            1 / Real.arccos (lam j) ^ 2
          let T := (1 / 2 : ℝ) * ∑ j ∈ Finset.univ.filter (fun j : Fin n => 1 ≤ (j : ℕ)),
            1 / (1 - lam j)
          let L := Real.log (n / (δ * ϵ * θl)) ^ K
          ENNReal.ofReal (1 - δ) ≤ alg.successProb OP
              (fun _ ρ => traceDist ρ (pureDM fun x => sqrtStationary π x) ≤ ϵ) ∧
          alg.expQueries OP ≤ ENNReal.ofReal (C * Real.sqrt (1 / θl ^ 2 + S) * L) ∧
          (∀ κ : ℝ, 1 ≤ κ → (∃ j : Fin n, 1 ≤ (j : ℕ) ∧ Real.arccos (lam j) ≤ κ * θl) →
            alg.expQueries OP ≤ ENNReal.ofReal (C * κ * Real.sqrt S * L)) ∧
          S ≤ T ∧
          (∀ κ : ℝ, 1 ≤ κ → (∃ j : Fin n, 1 ≤ (j : ℕ) ∧ Real.arccos (lam j) ≤ κ * θl) →
            alg.expQueries OP ≤ ENNReal.ofReal (C * κ * Real.sqrt T * L)) := by sorry

end GapAgnosticGS.Supplement
