-- Prove2me | Theorems.Thm_LimitedEntanglementTomography_LowerBound_proposition_7_1
-- name    : LimitedEntanglementTomography.LowerBound.proposition_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:04.193254+00:00
-- url     : https://prove2.me/theorems/f8cff0bd-2dfb-4c94-a12a-8513d621db41
-- title:
--   Proposition 7.1 — information bounds (51)–(53) for an adaptive protocol
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every protocol of Definition 1.1 (measurements on at most $k$ copies) that uses at most $n$ copies almost surely. Write $S=\sum_{j=1}^Tt_j\sqrt{\min\{t_j,d^2\}}$ for the weighted block count of the transcript $Y$.
--
--   1. At every state $\rho\succeq I_d/(4d)$,
--   $$\operatorname{tr}J_Y(\rho)\le C\,d^2\,\mathbb E_\rho S\qquad\text{and}\qquad\mathbb E_\rho S\le n\sqrt{\min\{k,d^2\}} .$$
--   2. For the prior $\mu$ of §6.1 (any $C_*\ge2$, $\varepsilon>0$, $\tau=C_*\varepsilon$) and a fixed state $\rho_\star$ with $\rho_\star+\Delta\succeq I_d/(4d)$ for every $\Delta\in K$, let $\Delta\sim\mu$ and let $Y$ be the transcript on input $\rho_\star+\Delta$. Then
--   $$I(\Delta;Y)\le\frac{\tau^2}{d^3}\,\mathbb E_{\Delta\sim\mu}\operatorname{tr}J_Y(\rho_\star+\Delta),$$
--   and consequently
--   $$I(\Delta;Y)\le C\,\frac{\tau^2}{d}\,\mathbb E_{\Delta,Y}S\qquad\text{and}\qquad\frac{\tau^2}{d}\,\mathbb E_{\Delta,Y}S\le\frac{\tau^2n}{d}\sqrt{\min\{k,d^2\}} .$$
--
--   This is the upper bound on the information an adaptive protocol acquires about the random state.
--
--   Differences from the source:
--   - generalization: (52)–(53) for the one constant C_* fixed in Proposition 6.1 → (52)–(53) for every C_* ≥ 2 (the standing assumption of §6.1) and every ε > 0; reason: the proof uses only the log-Sobolev inequality (43), which holds for every C_* ≥ 2 by Corollary 4.22 since K is closed, convex and has nonempty interior; the source's C_* is one instance
--   - encoding: Definition 1.1: rounds j = 1,…,T with 1 ≤ t_j ≤ k, a random stopping time, Σ t_j ≤ n almost surely → a protocol has a horizon `rounds`; a round with t_j = 0 makes no measurement (this encodes stopping); the outcome kernels are part of the data and are pinned to the Born laws on every state; Σ t_j ≤ n almost surely under every state; one standard Borel outcome space Out serves every round, and the POVM effects are measurable in the whole history; reason: T ≤ n since active rounds use at least one copy, so a horizon loses nothing; a round with t_j = 0 followed by measuring rounds is equivalent to the same protocol without that round, so the class of experiments is unchanged; the kernel exists and is unique on states for every source protocol; every standard Borel outcome space embeds Borel-isomorphically into one (for instance into ℝ), and a POVM family measurable on the histories with t_j = t extends to all histories by a fixed POVM
--   - encoding: tr J = E‖s_θ‖² with the score of the density p_θ = tr(K R_θ) (§4.2) → supremum over measurable maps φ into finite sets of the Fisher information of φ(Y), with values in [0,∞] (povmFisherTrace / Protocol.fisherTrace); reason: equal to the source quantity by the source's own Fact 4.3, eq. (16); extended values exclude any junk zero, and a non-differentiable outcome probability counts as +∞
--   - encoding: one fixed Frobenius-orthonormal basis F_1,…,F_{d²−1} of Herm₀(ℂ^d) → the statement holds for every orthonormal basis F (IsHerm0ONB F); reason: the source fixes an arbitrary such basis, so its claim is the same claim for every basis; trace Fisher information and the standard Gaussian law do not depend on the basis
--   - encoding: random matrices and sets in Herm₀(ℂ^d) → coordinates θ ∈ ℝ^{d²−1} with Δ = ∑_b θ_b F_b (herm0Coord); reason: an isometric linear bijection for the Frobenius norm; laws and events correspond one to one
--   - encoding: probabilities and expectations of nonnegative quantities in ℝ → values of measures in [0,∞] (ENNReal); reason: a probability is the same number; inequalities are unchanged
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, §7, printed p.26 / PDF p.28, Proposition 7.1 (eqs. (51)–(53))

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Prior

open scoped ENNReal ComplexOrder

/-!
Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, *Tight Lower Bounds for State
Tomography with Limited Entanglement*, STOC 2027 submission #1625 (October 2026), Proposition 7.1, printed p.26 / PDF p.28, eqs. (51)–(53).
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix ShadowTomography.ClassicalLB

/-- **Proposition 7.1.** There is an absolute constant `C > 0` such that, for every protocol of
Definition 1.1 using at most `n` copies almost surely, with `S = ∑_{j=1}^T t_j √(min{t_j, d²})`:
* (51) at every state `ρ ⪰ I_d/(4d)`: `tr J_Y(ρ) ≤ C d² E_ρ S` and `E_ρ S ≤ n √(min{k, d²})`;
* for the prior of §6.1 (any `C_* ≥ 2`, `ε > 0`, `τ = C_* ε`) and a fixed state `ρ_⋆` with
  `ρ_⋆ + Δ ⪰ I_d/(4d)` for every `Δ ∈ K`, with `Δ ∼ μ` and `Y` the transcript on `ρ_⋆ + Δ`:
  (52) `I(Δ; Y) ≤ (τ²/d³) E_{Δ∼μ} tr J_Y(ρ_⋆ + Δ)`, and
  (53) `I(Δ; Y) ≤ C (τ²/d) E_{Δ,Y} S` and `(τ²/d) E_{Δ,Y} S ≤ (τ² n/d) √(min{k, d²})`. -/
theorem proposition_7_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d k n : ℕ) (P : Protocol d k), P.UsesAtMost n →
      ∀ F : Fin (d ^ 2 - 1) → Op d, IsHerm0ONB F →
        (∀ ρ : Op d, WildeQIT.IsDensityOperator ρ → LoewnerGE ρ (1 / (4 * (d : ℝ))) →
          P.fisherTrace F ρ ≤ ENNReal.ofReal (C * (d : ℝ) ^ 2 * ∫ h, P.blockWeight h ∂(P.law ρ)) ∧
          ∫ h, P.blockWeight h ∂(P.law ρ) ≤ n * Real.sqrt (min (k : ℝ) ((d : ℝ) ^ 2))) ∧
        (∀ Cstar : ℝ, 2 ≤ Cstar → ∀ ε : ℝ, 0 < ε → ∀ ρstar : Op d,
          WildeQIT.IsDensityOperator ρstar →
          (∀ θ ∈ priorK F Cstar ε, LoewnerGE (ρstar + herm0Coord F θ) (1 / (4 * (d : ℝ)))) →
          mutualInfo (jointLaw (prior F Cstar ε) P F ρstar) ≤
              ENNReal.ofReal ((Cstar * ε) ^ 2 / (d : ℝ) ^ 3) *
                ∫⁻ θ, P.fisherTrace F (ρstar + herm0Coord F θ) ∂(prior F Cstar ε) ∧
          mutualInfo (jointLaw (prior F Cstar ε) P F ρstar) ≤
              ENNReal.ofReal (C * ((Cstar * ε) ^ 2 / d) *
                ∫ p, P.blockWeight p.2 ∂(jointLaw (prior F Cstar ε) P F ρstar)) ∧
          (Cstar * ε) ^ 2 / d * ∫ p, P.blockWeight p.2 ∂(jointLaw (prior F Cstar ε) P F ρstar) ≤
              (Cstar * ε) ^ 2 * n / d * Real.sqrt (min (k : ℝ) ((d : ℝ) ^ 2))) := by sorry

end LimitedEntanglementTomography.LowerBound
