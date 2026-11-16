-- Prove2me | Theorems.Thm_MulticalibrationGGM_Reduction_Supplement_theorem_5
-- name    : MulticalibrationGGM.Reduction.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:41:48.536759+00:00
-- url     : https://prove2.me/theorems/e609ca08-bf4e-4f46-b769-e951d3b2325d
-- title:
--   Theorem 5 — Φ-regret of best responses is at most the $H_\Phi$-multicalibration error
-- statement:
--   Let $Z\subseteq\mathbb R^d$ be a compact convex set of actions, $L\subseteq\mathbb R^d$ a convex set of losses, and $\Phi\subseteq\{Z\to Z\}$ any family of deviations. Let $\sigma:L\to Z$ be a best-response map, $\sigma(p)\in\arg\min_{z\in Z}p^\top z$, with arbitrary deterministic tie-breaking. For $\phi\in\Phi$ put $h_\phi(p)=\sigma(p)-\phi(\sigma(p))$.
--
--   Let $T$ be a horizon, $D_1,\dots,D_T$ probability laws on $L$, and $\ell_1,\dots,\ell_T\in L$ losses. Let $\mu_t$ be the pushforward of $D_t$ under $\sigma$, the law of $z_t=\sigma(p_t)$ with $p_t\sim D_t$. Assume the expectations below are defined. Then:
--
--   1. For every $\phi\in\Phi$, $$\Phi\text{-}\mathrm{Regret}_T(\phi)=\sum_{t=1}^T\mathbb E_{z_t\sim\mu_t}\big[\ell_t^\top(z_t-\phi(z_t))\big]\le\sum_{t=1}^T\mathbb E_{p_t\sim D_t}\big[h_\phi(p_t)^\top(\ell_t-p_t)\big]=\mathrm{MC\text{-}Err}_T(h_\phi).$$
--   2. In particular, $$\mathrm{Regret}^\Phi_T=\sup_{\phi\in\Phi}\Phi\text{-}\mathrm{Regret}_T(\phi)\le\sup_{h\in H_\Phi}\mathrm{MC\text{-}Err}_T(h)=\mathrm{MC\text{-}Err}_T,$$ with both suprema taken in the extended reals.
--
--   The inequality holds for every sequence of laws and losses, so it covers every run of Algorithm 2, where $D_t$ is the forecaster's output and $\ell_t$ is revealed by Nature. Sublinear multicalibration error with respect to $H_\Phi$ therefore gives sublinear Φ-regret for the decision maker who best-responds to the forecasts. This is a companion theorem and is not used in the proof of Theorem 4.
--
--   Differences from the source:
--   - generalization: D_t is the sequence produced in Algorithm 2 by a forecaster multicalibrated with respect to H_Φ, and ℓ_t are Nature's losses → arbitrary probability laws D_t on L and arbitrary losses ℓ_t ∈ L; reason: the inequality is pathwise, and every run of Algorithm 2 gives such sequences
--   - generalization: horizons T ≥ 1 → every T ∈ ℕ, including T = 0; reason: at T = 0 both sums are empty, and the statement for T ≥ 1 is unchanged
--   - reading: the display's "h(p_t)" → h_ϕ(p_t); reason: the display defines MC-Err_T(h_ϕ) on the same line
--   - encoding: σ(p) := argmin_{z∈Z} pᵀz with ties broken deterministically by an arbitrary scheme → any function σ : L → Z with σ(p) minimizing pᵀz over Z; reason: these are exactly the possible tie-breaking schemes
--   - encoding: expectations are well defined → σ almost-everywhere measurable for each D_t, with the regret integrand integrable under μ_t and the multicalibration payoff integrable under D_t, for every ϕ ∈ Φ and every round; reason: these make the displayed expectations and the pushforward meaningful; without measurability Mathlib's pushforward is the zero measure
--   - encoding: tests (x, p) ↦ σ(p) − ϕ(σ(p)) on X × Y → context-free tests on the one-point context type Unit; reason: the tests do not depend on the context
--   - encoding: the shorthands Regret^Φ_T := sup_ϕ and MC-Err_T := sup_{h ∈ H_Φ} → suprema in EReal; reason: Φ may be infinite and the families unbounded; the empty supremum is ⊥ on both sides
--   - encoding: vectors in ℝ^d, Z and L subsets → Fin d coordinates, subtypes of Fin d → ℝ, Borel probability measures on the subtype L; reason: Lean representation
-- source:
--   Gabriele Farina, Juan Perdomo, An Efficient Black-Box Reduction from Online Learning to Multicalibration, and a New Route to Φ-Regret Minimization, STOC 2027 submission #721 (October 2026), Theorem 5, p. 15 (proof pp. 15–16); Definition 2, p. 5; Equation (4), p. 14; Algorithm 2, p. 15. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf. PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.

import Mathlib
import Definitions.Def_MulticalibrationGGM_Reduction_Model
import Definitions.Def_MulticalibrationGGM_Reduction_Supplement_Forecaster
import Definitions.Def_MulticalibrationGGM_Reduction_Supplement_PhiRegret

open MeasureTheory

namespace MulticalibrationGGM.Reduction.Supplement

/-- Farina and Perdomo, STOC 2027 submission #721 (October 2026), Theorem 5, p. 15
(proof pp. 15–16), with Definition 2 (p. 5), Equation (4) (p. 14) and Algorithm 2 (p. 15).
https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf
PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.

Pathwise over every sequence of forecast laws `D_t` on `L` and losses `ℓ_t ∈ L`
(round `t` of `R`, with outcome `ℓ_t`), hence over every run of Algorithm 2: with
`µ_t = σ#D_t` and `h_ϕ = σ − ϕ ∘ σ`, (a) `Φ-Regret_T(ϕ) ≤ MC-Err_T(h_ϕ)` for every
`ϕ ∈ Φ`, and (b) `sup_{ϕ ∈ Φ} Φ-Regret_T(ϕ) ≤ sup_{h ∈ H_Φ} MC-Err_T(h)` in `EReal`.
The hypotheses `hσ`, `hreg`, `hmc` state that the source's expectations are defined. -/
theorem theorem_5 {d : ℕ} (Z L : Set (Vector d))
    (hZcompact : IsCompact Z) (hZconvex : Convex ℝ Z) (hLconvex : Convex ℝ L)
    (Φ : Set (Z → Z)) (σ : L → Z) (hσbr : IsBestResponseMap σ)
    (R : ℕ → FRound Unit L) (T : ℕ)
    (hσ : ∀ t ∈ Finset.Icc 1 T, AEMeasurable σ ((R t).forecast : Measure L))
    (hreg : ∀ ϕ ∈ Φ, ∀ t ∈ Finset.Icc 1 T,
      Integrable (deviationLoss (R t).outcome ϕ) (actionLaw σ (R t).forecast))
    (hmc : ∀ ϕ ∈ Φ, ∀ t ∈ Finset.Icc 1 T,
      Integrable (payoff (hPhi σ ϕ) () (R t).outcome) ((R t).forecast : Measure L)) :
    (∀ ϕ ∈ Φ, phiRegret σ R T ϕ ≤ roundsMCError R T (hPhi σ ϕ)) ∧
    phiRegretSup σ Φ R T ≤ mcErrorSup (HPhi σ Φ) R T := by sorry

end MulticalibrationGGM.Reduction.Supplement
