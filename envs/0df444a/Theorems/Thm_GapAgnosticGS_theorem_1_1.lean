-- Prove2me | Theorems.Thm_GapAgnosticGS_theorem_1_1
-- name    : GapAgnosticGS.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:00.858807+00:00
-- url     : https://prove2.me/theorems/2b1e813e-81c2-4a20-a5b6-a45a111c9e7c
-- title:
--   Theorem 1.1 — gap-agnostic ground-state preparation with $O(\alpha\sqrt{\Gamma_{\rm gs}}\,\mathrm{polylog})$ expected queries, tight for some families
-- statement:
--   Let $H$ act on $\mathbb C^n$, $n\ge2$, with eigenvalues $E_0\le E_1\le\dots\le E_{n-1}$ in $[-\alpha,\alpha]$ ($\alpha>0$ known), accessed only through controlled uses of $W_H=e^{i\pi H/(4\alpha)}$ and $W_H^\dagger$ (one query each). For a unique ground state $|\phi_0\rangle$ let $\Delta_{\rm gs}=E_1-E_0$, $\Gamma_{\rm gs}=\sum_{j\ge1}(E_j-E_0)^{-2}$ and $d_{\rm eff}=\Delta_{\rm gs}^2\Gamma_{\rm gs}$.
--
--   1. **Upper bound.** There are absolute constants $C>0$, $K\in\mathbb N$ such that for every $n\ge2$, $\alpha>0$ and $\epsilon,\delta\in(0,1/3)$ there is one algorithm, using no knowledge of $H$, of $\Delta_{\rm gs}$, of $\Gamma_{\rm gs}$ or of any guiding state, such that for every Hamiltonian $H$ as above with a unique ground state: with probability at least $1-\delta$ it outputs a state $\rho$ with $\langle\phi_0|\rho|\phi_0\rangle\ge1-\epsilon$, using at most
--   $$C\,\alpha\sqrt{\Gamma_{\rm gs}}\,\log^K\!\Big(\frac{n\alpha}{\delta\epsilon\Delta_{\rm gs}}\Big)=\widetilde O\Big(\frac{\alpha}{\Delta_{\rm gs}}\sqrt{d_{\rm eff}}\Big)$$
--   expected queries.
--   2. **Lower bound (Theorem 3.15).** There is an absolute constant $c>0$ such that for every $n\ge2$, $\alpha>0$, $\Delta\in(0,2\alpha]$ and $k\in\{2,\dots,n\}$ there is a nonempty family of Hamiltonians with norm at most $\alpha$, a unique ground state, spectral gap $\Delta$ and
--   $$d_{\rm eff}=(k-1)+(n-k)\Big(\frac{\Delta}{2\alpha}\Big)^2,$$
--   such that every algorithm that, on every member, outputs with probability at least $2/3$ a state of fidelity at least $9/10$ with the ground state makes at least $c\,(\alpha/\Delta)\sqrt{d_{\rm eff}}$ queries in the worst case on some member, and at least $c\,(\alpha/\Delta)\sqrt{d_{\rm eff}}$ expected queries on some member.
--
--   The upper bound adapts to the whole excitation spectrum through $\Gamma_{\rm gs}$; the lower bound shows that this dependence cannot be improved beyond polylogarithmic factors in general.
--
--   Differences from the source:
--   - reading: W_H = e^{iτH}, τ = Θ(1/α) → τ = π/(4α); reason: the paper's value (p.5, Lemma 3.1, and the proof of Theorem 3.15)
--   - reading: O(·), polylog(·), Ω(·) → absolute constants C, K (upper) and c (lower) chosen before every other quantity; polylog(x) = (log x)^K with K ∈ ℕ; reason: the standard meaning; the argument nα/(δϵ∆_gs) exceeds 9 on the domain
--   - reading: an algorithm; queries; expected queries (undefined in the paper) → the adaptive oracle model OracleAlg: oracle-independent data, controlled W_H and W_H† queries each counted once, mid-run measurements with quantum memory, history-dependent workspace, no depth bound; one model for both clauses; reason: the paper defines no model; this is the standard one, and Theorem 1.1 fixes expected queries as the cost of the upper bound
--   - reading: Moreover, there are families of Hamiltonians for which the query complexity is optimal up to polylogarithmic factors → Theorem 3.15 in full: for every n ≥ 2, α > 0, ∆ ∈ (0, 2α], k ∈ {2, …, n} a family with gap ∆ and d_eff = (k − 1) + (n − k)(∆/2α)² on which fidelity 9/10 with probability 2/3 requires c(α/∆)√d_eff worst-case and expected queries; reason: the abbreviated theorem points to Theorem 3.15, which states the families
--   - encoding: ‖H‖ ≤ α; a unique ground state |ϕ_0⟩ with gap ∆_gs > 0 → H Hermitian with every eigenvalue in [−α, α]; HasSimpleGroundState H (n ≥ 2, E_0 < E_1); reason: the spectral norm of a Hermitian matrix is its largest eigenvalue modulus; same instances
--   - encoding: ⟨ϕ_0|ρ|ϕ_0⟩ ≥ 1 − ϵ → the bound for every unit ground vector ϕ_0, with ρ the reduced output state; reason: under a unique ground state these vectors differ by a phase and give the same value
--   - encoding: expected and worst-case query counts → expected counts in ℝ≥0∞, worst-case counts in ℕ∞; reason: a non-halting algorithm is never counted as 0 queries
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1 (abbreviated), p.2 (PDF p.3); Corollary 3.11, p.13 (PDF p.14); Theorem 3.15, p.14 (PDF p.15); setting and access model, pp.1–2 (PDF pp.2–3)

import Definitions.Def_GapAgnosticGS_gammaGS
import Definitions.Def_GapAgnosticGS_deff
import Definitions.Def_GapAgnosticGS_phaseOracle
import Definitions.Def_GapAgnosticGS_OracleAlg_successProb
import Definitions.Def_GapAgnosticGS_OracleAlg_expQueries
import Definitions.Def_GapAgnosticGS_OracleAlg_maxQueries
open QAlgorithms

namespace GapAgnosticGS

open scoped ENNReal

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Theorem 1.1 (abbreviated), p.2 (PDF p.3): "Suppose ‖H‖ ≤ α and has a unique ground
state |ϕ_0⟩ with possibly unknown gap ∆_gs > 0. For every ϵ, δ ∈ (0, 1/3), an algorithm outputs,
with probability at least 1 − δ, a state ρ satisfying ⟨ϕ_0|ρ|ϕ_0⟩ ≥ 1 − ϵ, using
O(α√Γ_gs polylog(nα/(δϵ∆_gs))) = Õ((α/∆_gs)√d_eff) expected queries. Moreover, there are families
of Hamiltonians for which the query complexity is optimal up to polylogarithmic factors";
Theorem 3.15, p.14 (PDF p.15) (the "Moreover" in full): "For every n ≥ 2, α > 0,
∆_gs ∈ (0, 2α], and k ∈ {2, …, n}, there is a family of Hamiltonians with norm ≤ α, with spectral
gap ∆_gs, and d_eff = (k − 1) + (n − k)(∆_gs/2α)², such that preparing their ground states to
fidelity at least 9/10, with probability at least 2/3, requires Ω((α/∆_gs)√d_eff) queries in the
worst case. It also holds for worst-case expected query complexity." Setting, p.2: "Let H act on a
known n-dimensional Hilbert space, where n ≥ 2"; access model, p.1: "W_H = e^{iτH} … We assume
access to W_H, W_H†, and controlled versions of both; one controlled use of W_H or W_H† counts as
one query."

(a) **Upper bound.** There are absolute `C`, `K` such that for every `n ≥ 2`, `α > 0` and
`ϵ, δ ∈ (0, 1/3)` one algorithm, fixed before `H`, satisfies for every Hermitian `H` on `ℂⁿ` with a
unique ground state and all eigenvalues in `[−α, α]`: with probability at least `1 − δ` it halts
with an output state `ρ` with `⟨ϕ_0|ρ|ϕ_0⟩ ≥ 1 − ϵ` (for every unit ground vector `ϕ_0`), using at
most `C α √Γ_gs log^K(nα/(δϵ∆_gs))` expected queries to the phase oracle `W_H`, `τ = π/(4α)`.

(b) **Lower bound.** There is an absolute `c > 0` such that for every `n ≥ 2`, `α > 0`,
`∆ ∈ (0, 2α]` and `k ∈ {2, …, n}` there is a nonempty family of Hamiltonians with eigenvalues in
`[−α, α]`, a unique ground state, gap `∆` and `d_eff = (k − 1) + (n − k)(∆/(2α))²`, such that every
algorithm that prepares each member's ground state to fidelity at least `9/10` with probability at
least `2/3` makes at least `c (α/∆) √d_eff` queries on some member in the worst case, and at least
`c (α/∆) √d_eff` expected queries on some member.

**Formalization Note.** Algorithms are `OracleAlg (Fin n) (Fin n) Unit`: adaptive, with
mid-run measurements and quantum memory, a history-dependent workspace, no depth bound, and
controlled `W_H`/`W_H†` queries each counted once; the output state is the reduced state of the
output register `ℂⁿ`. "‖H‖ ≤ α" is `|E_j| ≤ α` for every eigenvalue. Expected counts are in
`ℝ≥0∞` and worst-case counts in `ℕ∞` (so a non-halting algorithm is never counted as `0`). The
fidelity of every unit ground vector is required; under a unique ground state they differ by a
phase and give the same value. -/
theorem theorem_1_1 :
    (∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ (α ϵ δ : ℝ), 0 < α → ϵ ∈ Set.Ioo 0 (1 / 3) →
        δ ∈ Set.Ioo 0 (1 / 3) →
      ∃ A : OracleAlg (Fin n) (Fin n) Unit,
        ∀ H : Matrix (Fin n) (Fin n) ℂ, HasSimpleGroundState H → (∀ j, |energy H j| ≤ α) →
          (∀ φ₀ : EuclideanSpace ℂ (Fin n), IsGroundState H φ₀ →
            ENNReal.ofReal (1 - δ) ≤ A.successProb (phaseOracle H α)
              (fun _ ρ => 1 - ϵ ≤ (inner ℂ φ₀ (act ρ φ₀)).re)) ∧
          A.expQueries (phaseOracle H α) ≤
            ENNReal.ofReal (C * α * Real.sqrt (gammaGS H) *
              Real.log (n * α / (δ * ϵ * spectralGap H)) ^ K)) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ (α Δ : ℝ), 0 < α → Δ ∈ Set.Ioc 0 (2 * α) →
      ∀ k : ℕ, 2 ≤ k → k ≤ n →
      ∃ F : Set (Matrix (Fin n) (Fin n) ℂ), F.Nonempty ∧
        (∀ H ∈ F, HasSimpleGroundState H ∧ (∀ j, |energy H j| ≤ α) ∧ spectralGap H = Δ ∧
          deff H = ((k : ℝ) - 1) + ((n : ℝ) - k) * (Δ / (2 * α)) ^ 2) ∧
        ∀ A : OracleAlg (Fin n) (Fin n) Unit,
          (∀ H ∈ F, ∀ φ₀ : EuclideanSpace ℂ (Fin n), IsGroundState H φ₀ →
            ENNReal.ofReal (2 / 3) ≤ A.successProb (phaseOracle H α)
              (fun _ ρ => 9 / 10 ≤ (inner ℂ φ₀ (act ρ φ₀)).re)) →
          (∃ H ∈ F, ENNReal.ofReal (c * (α / Δ) *
              Real.sqrt (((k : ℝ) - 1) + ((n : ℝ) - k) * (Δ / (2 * α)) ^ 2)) ≤
            ((A.maxQueries (phaseOracle H α) : ℕ∞) : ℝ≥0∞)) ∧
          (∃ H ∈ F, ENNReal.ofReal (c * (α / Δ) *
              Real.sqrt (((k : ℝ) - 1) + ((n : ℝ) - k) * (Δ / (2 * α)) ^ 2)) ≤
            A.expQueries (phaseOracle H α))) := by sorry

end GapAgnosticGS
