-- Prove2me | Theorems.Thm_KnownFidelity_Rank_lemma_2_1
-- name    : KnownFidelity.Rank.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:47:53.581223+00:00
-- url     : https://prove2.me/theorems/d8710396-5e8e-4a0f-8961-ae39e96f6a42
-- title:
--   Lemma 2.1 — two-prior principle
-- statement:
--   Let $\Pi_0,\Pi_1$ be priors on states on $\mathbb C^d$ and $T$ a real-valued functional with
--
--   $$T(\rho)\le\tau_-\ \ \Pi_0\text{-a.s.},\qquad T(\rho)\ge\tau_+\ \ \Pi_1\text{-a.s.},\qquad \tau_+-\tau_->2\varepsilon .$$
--
--   If the $n$-copy average states satisfy $d_{\mathrm{tr}}\big(\mathbb E_{\Pi_0}\rho^{\otimes n},\mathbb E_{\Pi_1}\rho^{\otimes n}\big)<1/3$, then no estimator on $n$ copies can estimate $T$ to additive error $\varepsilon$ with success probability at least $2/3$ on (almost) every state of the two priors.
--
--   This is the standard reduction from estimation to testing, combined with Helstrom's bound; it converts Lemma 4.2 into copy lower bounds.
--
--   Differences from the source:
--   - generalization: no estimator succeeds on every state in the two supports → no estimator succeeds on Π₀-almost every and Π₁-almost every state; reason: requiring success only almost surely is a weaker hypothesis on the estimator, so the impossibility is stronger; it implies the printed form
--   - generalization: additive error ε (ε > 0 implicit) → every real ε; reason: for ε ≤ 0 the conclusion still holds; the source's case is included
--   - encoding: an estimator on n copies → an OperatorPOVM on (ℂ^d)^{⊗n} with real outcomes; reason: a collective measurement followed by classical post-processing is such a POVM
--   - encoding: priors Π₀, Π₁ on states and their n-copy average states → IsStatePrior (probability measure, a.s. a density matrix) and avgPower Π id n (entrywise integrals of ρ^{⊗n}); reason: the same objects; the a.s. state condition keeps every integral genuine
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Lemma 2.1, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_IsStatePrior
import Definitions.Def_KnownFidelity_Rank_avgPower
import Definitions.Def_KnownFidelity_Rank_traceDist
import Definitions.Def_KnownFidelity_Rank_copyLaw

open MeasureTheory

namespace KnownFidelity.Rank

/-- **Lemma 2.1 (Two-prior principle).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Lemma 2.1, printed p. 4 (PDF p. 6): "Let Π₀, Π₁ be priors on states such that a
real-valued functional T satisfies T(ρ) ≤ τ₋ Π₀-a.s., T(ρ) ≥ τ₊ Π₁-a.s., where τ₊ − τ₋ > 2ε. If
the corresponding n-copy average states have trace distance less than 1/3, then no estimator can
estimate T to additive error ε with success probability at least 2/3 on every state in the two
supports."

For priors `Π₀, Π₁` on states on `ℂ^d`, any `T`, thresholds with `τ₊ − τ₋ > 2ε` and
`d_tr(E_{Π₀} ρ^{⊗n}, E_{Π₁} ρ^{⊗n}) < 1/3`, there is no POVM on `n` copies with real outcomes
whose outcome lies within `ε` of `T(ρ)` with probability at least `2/3` for `Π₀`-almost every and
`Π₁`-almost every state `ρ`.

**Formalization Note.** "On every state in the two supports" is weakened to almost every state
of each prior, which makes the lemma stronger (every state of the support is in particular almost
every state). An estimator is any `OperatorPOVM` on `(ℂ^d)^{⊗n}` with real outcomes; the average
states are `avgPower P_b id n`. -/
theorem lemma_2_1 {d n : ℕ} (P₀ P₁ : Measure (Matrix (Fin d) (Fin d) ℂ))
    (hP₀ : IsStatePrior P₀) (hP₁ : IsStatePrior P₁) (T : Matrix (Fin d) (Fin d) ℂ → ℝ)
    (τm τp ε : ℝ) (hT₀ : ∀ᵐ ρ ∂P₀, T ρ ≤ τm) (hT₁ : ∀ᵐ ρ ∂P₁, τp ≤ T ρ)
    (hgap : 2 * ε < τp - τm)
    (hdist : traceDist (avgPower P₀ id n) (avgPower P₁ id n) < 1 / 3) :
    ¬ ∃ E : QAlgorithms.Measurements.OperatorPOVM (Fin n → Fin d) ℝ,
      (∀ᵐ ρ ∂P₀, ∃ hρ : QAlgorithms.IsDensityMatrix ρ,
        ENNReal.ofReal (2 / 3) ≤ copyLaw n E ρ hρ {x : ℝ | |x - T ρ| ≤ ε}) ∧
      (∀ᵐ ρ ∂P₁, ∃ hρ : QAlgorithms.IsDensityMatrix ρ,
        ENNReal.ofReal (2 / 3) ≤ copyLaw n E ρ hρ {x : ℝ | |x - T ρ| ≤ ε}) := by sorry

end KnownFidelity.Rank
