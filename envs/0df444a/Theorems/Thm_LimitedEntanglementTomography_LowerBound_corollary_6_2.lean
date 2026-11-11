-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_corollary_6_2
-- name    : LimitedEntanglementTomography.LowerBound.corollary_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:42.398525+00:00
-- url     : https://prove2.me/theorems/2b42dcbc-b1bc-4673-ba4f-9cfa87a613bb
-- title:
--   Corollary 6.2 — accurate tomography under the prior needs $I(\Delta;Y)\gtrsim d^2$
-- statement:
--   There are absolute constants $C_1\ge2$, $c>0$ and $d_0$ such that the following holds for every admissible $C_*\ge C_1$, every $d\ge d_0$ and every $\varepsilon>0$. Let $\rho_\star$ be a fixed state such that $\rho_\star+\Delta$ is a state for every $\Delta\in K$, let $\Delta\sim\mu$ (the prior of §6.1), and let $Y$ be the transcript of a protocol of Definition 1.1 on input $\rho_\star+\Delta$. If, for some $\tfrac12\le q\le1$, an estimator $\hat\rho(Y)$ satisfies
--   $$\Pr\big[D_{\mathrm{tr}}(\rho_\star+\Delta,\hat\rho(Y))\le\varepsilon\big]\ge q,$$
--   then
--   $$I(\Delta;Y)\ge c\,d^2 .$$
--
--   The success hypothesis is averaged over the prior, unlike the worst-case success of Problem 1.2.
--
--   Differences from the source:
--   - generalization: one absolute C_* ≥ 2 fixed in Proposition 6.1 and used for the rest of the paper → every C_* ≥ C₁ for one absolute C₁ ≥ 2, with the remaining constants (c, d₀) uniform in C_*; reason: the proof of Corollary 6.2 (through (44)) uses only C_*/√2 ≥ C₀ and √2/C_* ≤ c₀/2, both monotone in C_*; taking C_* = C₁ recovers the source statement, and the uniformity lets Proposition 6.1, Corollary 6.2 and the main proof share one C_*
--   - encoding: Definition 1.1: rounds j = 1,…,T with 1 ≤ t_j ≤ k, a random stopping time, Σ t_j ≤ n almost surely → a protocol has a horizon `rounds`; a round with t_j = 0 makes no measurement (this encodes stopping); the outcome kernels are part of the data and are pinned to the Born laws on every state; Σ t_j ≤ n almost surely under every state; one standard Borel outcome space Out serves every round, and the POVM effects are measurable in the whole history; reason: T ≤ n since active rounds use at least one copy, so a horizon loses nothing; a round with t_j = 0 followed by measuring rounds is equivalent to the same protocol without that round, so the class of experiments is unchanged; the kernel exists and is unique on states for every source protocol; every standard Borel outcome space embeds Borel-isomorphically into one (for instance into ℝ), and a POVM family measurable on the histories with t_j = t extends to all histories by a fixed POVM
--   - encoding: one fixed Frobenius-orthonormal basis F_1,…,F_{d²−1} of Herm₀(ℂ^d) → the statement holds for every orthonormal basis F (IsHerm0ONB F); reason: the source fixes an arbitrary such basis, so its claim is the same claim for every basis; trace Fisher information and the standard Gaussian law do not depend on the basis
--   - encoding: random matrices and sets in Herm₀(ℂ^d) → coordinates θ ∈ ℝ^{d²−1} with Δ = ∑_b θ_b F_b (herm0Coord); reason: an isometric linear bijection for the Frobenius norm; laws and events correspond one to one
--   - encoding: probabilities and expectations of nonnegative quantities in ℝ → values of measures in [0,∞] (ENNReal); reason: a probability is the same number; inequalities are unchanged
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §6, printed p.24 / PDF p.26, Corollary 6.2 (eq. (45))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Prior

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Corollary 6.2, printed p.24 / PDF p.26, eq. (45).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Corollary 6.2.** There are absolute `C₁ ≥ 2`, `c > 0` and `d₀` such that for every admissible
`C_* ≥ C₁`, every `d ≥ d₀`, every `ε > 0`, and every fixed state `ρ_⋆` with `ρ_⋆ + Δ` a state for
every `Δ ∈ K`: if `Δ ∼ μ`, `Y` is the transcript of a protocol on input `ρ_⋆ + Δ`, and for some
`1/2 ≤ q ≤ 1` an estimator satisfies `Pr[D_tr(ρ_⋆ + Δ, ρ̂(Y)) ≤ ε] ≥ q`, then `I(Δ; Y) ≥ c d²`. -/
theorem corollary_6_2 :
    ∃ C₁ : ℝ, 2 ≤ C₁ ∧ ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
      ∀ Cstar : ℝ, C₁ ≤ Cstar → ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε →
      ∀ F : Fin (d ^ 2 - 1) → Op d, IsHerm0ONB F →
      ∀ ρstar : Op d, WildeQIT.IsDensityOperator ρstar →
        (∀ θ ∈ priorK F Cstar ε, WildeQIT.IsDensityOperator (ρstar + herm0Coord F θ)) →
      ∀ (k : ℕ) (P : Protocol d k) (est : P.Estimator) (q : ℝ), 1 / 2 ≤ q → q ≤ 1 →
        ENNReal.ofReal q ≤ jointLaw (prior F Cstar ε) P F ρstar
            {p | traceDist (ρstar + herm0Coord F p.1) (est.toFun p.2) ≤ ε} →
        ENNReal.ofReal (c * (d : ℝ) ^ 2) ≤ mutualInfo (jointLaw (prior F Cstar ε) P F ρstar) := by sorry

end LimitedEntanglementTomography.LowerBound
