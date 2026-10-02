-- Prove2me | Theorems.Thm_MDPFinance_JumpMarkets_proposition_9_3_3
-- name    : MDPFinance.JumpMarkets.proposition_9_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:28:16.772315+00:00
-- url     : https://prove2.me/theorems/4364a795-cb8e-4a1a-a67f-8e16ac7bacf4
-- title:
--   Proposition 9.3.3 — IM_cv and Δ satisfy the assumptions of Theorem 7.3.5
-- statement:
--   **Proposition 9.3.3** (p. 285). The sets $IM_{cv}$ and
--   $\Delta := \{f : E \to A \text{ measurable}\}$ satisfy the assumptions of Theorem 7.3.5.
--
--   A one-line statement whose proof runs a page and a half, and the hinge of the section: it is what
--   lets Theorem 9.3.4 quote Chapter 7's Structure Theorem instead of redoing it. Theorem 7.3.5's
--   hypotheses are restated locally, since chunk `07a`'s Lean is a different mission: $IM_{cv}$ is a
--   $\|\cdot\|_b$-closed subset of $IB_b$, $\mathcal{T}$ maps $IM_{cv}$ into itself, and every
--   $v \in IM_{cv}$ admits a maximizer in $\Delta$.
--
--   **Condition (i) is instantiated with $U$, not with $0$.** The book is explicit: "It is clear that
--   $U \in IM_{cv}$. Here we choose $U$ instead of $v = 0$ since the Markov Decision Model is
--   contracting" (p. 286). Since every member of $IM_{cv}$ dominates $U$ and $U$ is strictly
--   increasing, $0 \notin IM_{cv}$, so the substitution is not cosmetic — stating the condition as
--   $0 \in IM_{cv}$ would make the proposition false.
--
--   The concavity half of "$\mathcal{T}$ maps $IM_{cv}$ into itself" is the part that needs work, and
--   the book changes coordinates to get it: fractions $\alpha$ are replaced by invested amounts
--   $a_t := \alpha_t\phi^\alpha_t(x)$, in which $(x,a) \mapsto \phi^a_t(x)$ is **linear** and hence
--   $(x,a) \mapsto Lv(t,x,a)$ concave.
--
--   **Moderation note.** Condition (iii) of Theorem 7.3.5 asks for a maximizer in `Δ = {f : E → A measurable}`; the draft's maximizer was an arbitrary map. Now `f` is measurable for the Borel σ-algebra of the Young topology on `A`, and the maximum-point set is the `[0,∞]`-valued one.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 285 (PDF 295), Proposition 9.3.3

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.JumpMarkets

/-- **Proposition 9.3.3** (p. 285). Under a bounding function `b = b_γ` with `α_b < 1`, the sets
`IM_cv` and `Δ := {f : E → A measurable}` satisfy the assumptions of Theorem 7.3.5: (i) `U ∈
IM_cv` (chosen instead of `0`, which is not in `IM_cv`), `IM_cv` is a `‖·‖_b`-closed subset of
`IB_b`; (ii) `𝒯 : IM_cv → IM_cv`; (iii) every `v ∈ IM_cv` has a maximizer `f ∈ Δ`. -/
theorem proposition_9_3_3 {d : ℕ} (M : JumpMarket d) (gamma : ℝ) (alpha : ℝ)
    (hb : M.IsBoundingFunction (M.bfun gamma) alpha) (halpha : alpha < 1) :
    (M.IMcv (M.bfun gamma) (fun p => M.U p.2)) ∧
    (∀ (vn : ℕ → ℝ × ℝ → ℝ) (v : ℝ × ℝ → ℝ), (∀ n, M.IMcv (M.bfun gamma) (vn n)) →
      (∃ C : ℝ, ∀ p ∈ M.E, |v p| ≤ C * M.bfun gamma p) →
      (∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ p ∈ M.E, |vn n p - v p| ≤ ε * M.bfun gamma p) →
      M.IMcv (M.bfun gamma) v) ∧
    (∀ v w : ℝ × ℝ → ℝ, M.IMcv (M.bfun gamma) v → M.IsTOf v w → M.IMcv (M.bfun gamma) w) ∧
    (∀ v : ℝ × ℝ → ℝ, M.IMcv (M.bfun gamma) v →
      ∃ f : ℝ × ℝ → Control d, Measurable f ∧
        ∀ p ∈ M.E, f p ∈ M.Astar (fun q => ENNReal.ofReal (v q)) p) := by sorry

end MDPFinance.JumpMarkets
