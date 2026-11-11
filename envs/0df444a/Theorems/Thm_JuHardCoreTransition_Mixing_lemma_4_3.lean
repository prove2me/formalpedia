-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_lemma_4_3
-- name    : JuHardCoreTransition.Mixing.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:51.130478+00:00
-- url     : https://prove2.me/theorems/a8243b4a-83f2-440c-93da-781ae1920125
-- title:
--   Lemma 4.3 — subcritical field-dynamics spectral stability
-- statement:
--   Let $d\ge3$ and let $G$ have maximum degree at most $d$. For each $0<a<\lambda_c(d)$ define $\theta_d(a)\in(0,1/(d-1))$ by $a=\theta_d(a)/(1-\theta_d(a))^d$. Then for every $0<\lambda<\lambda_c(d)$ the hard-core distribution $\mu_{G,\lambda}$ satisfies field-dynamics spectral stability (Definition 4.1) with rate
--   $$\mathcal C(a)=\frac1{1-(d-1)\theta_d(a)}\le\frac{2(1+1/(d-2))}{1-a/\lambda_c(d)},\qquad0<a\le\lambda .$$
--
--   Differences from the source:
--   - reading: define θ_d(a) ∈ (0, 1/(d−1)) by a = θ_d(a)/(1 − θ_d(a))^d → a first conjunct asserting that this root exists and is unique for 0 < a < λ_c(d); thetaD is that root; reason: the definition presupposes existence and uniqueness; stating it keeps thetaD from taking its junk value
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Lemma 4.3, printed p.19 / PDF p.20

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-- **Lemma 4.3 (Subcritical spectral stability)** (printed p.19 / PDF p.20). Let `d ≥ 3` and let
`G` have maximum degree at most `d`. For each `0 < a < λ_c(d)`, `θ_d(a) ∈ (0, 1/(d−1))` is defined
by `a = θ_d(a)/(1 − θ_d(a))^d` (the first conjunct: this root exists and is unique). Then for every
`0 < λ < λ_c(d)`, `μ_{G,λ}` satisfies field-dynamics spectral stability (Definition 4.1) with rate
`C(a) = 1/(1 − (d−1)θ_d(a))`, and `C(a) ≤ 2(1 + 1/(d−2))/(1 − a/λ_c(d))` for `0 < a ≤ λ` (4.4). -/
theorem lemma_4_3 (d : ℕ) (hd : 3 ≤ d) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, G.degree v ≤ d) :
    (∀ a : ℝ, 0 < a → a < lamCrit d →
      ∃! θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (1 / ((d : ℝ) - 1)) ∧ a = θ / (1 - θ) ^ d) ∧
    ∀ lam : ℝ, 0 < lam → lam < lamCrit d →
      IsStabilityRate G lam (fun a => 1 / (1 - ((d : ℝ) - 1) * thetaD d a)) ∧
      ∀ a : ℝ, 0 < a → a ≤ lam →
        1 / (1 - ((d : ℝ) - 1) * thetaD d a) ≤
          2 * (1 + 1 / ((d : ℝ) - 2)) / (1 - a / lamCrit d) := by sorry

end JuHardCoreTransition.Mixing
