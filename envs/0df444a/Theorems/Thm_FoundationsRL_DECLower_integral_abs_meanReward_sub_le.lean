-- Prove2me | Theorems.Thm_FoundationsRL_DECLower_integral_abs_meanReward_sub_le
-- name    : FoundationsRL.DECLower.integral_abs_meanReward_sub_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:19:42.645098+00:00
-- url     : https://prove2.me/theorems/fc9d9b2f-5f46-42ef-9be9-fc106baac1e5
-- title:
--   (6.40) — $\mathbb E_p|f^M-f^{\widehat M}|\le\mathbb E_p D_{\mathrm{TV}}(M,\widehat M)\le\sqrt{\mathbb E_p D^2_{\mathrm H}(M,\widehat M)}$
-- statement:
--   Let $M$ and $\widehat M$ be models (rewards in $[0,1]$) and let $p$ be a probability distribution on decisions such that $\pi\mapsto D_{\mathrm{TV}}(M(\pi),\widehat M(\pi))$ and $\pi\mapsto D^2_{\mathrm H}(M(\pi),\widehat M(\pi))$ are measurable. Then
--
--   $$
--   \mathbb E_{\pi\sim p}\bigl|f^M(\pi)-f^{\widehat M}(\pi)\bigr|\le\mathbb E_{\pi\sim p}\bigl[D_{\mathrm{TV}}(M(\pi),\widehat M(\pi))\bigr]\le\sqrt{\mathbb E_{\pi\sim p}\bigl[D^2_{\mathrm H}(M(\pi),\widehat M(\pi))\bigr]}.
--   $$
--
--   Since rewards are bounded, mean rewards of two models differ by at most their total variation distance, and the Hellinger constraint of the constrained DEC therefore bounds the difference of mean rewards under the reference model's action distribution.
--
--   Differences from the source:
--   - generalization: $\mathbb E_{\pi\sim p_{\widehat M}}[f^M(\pi)-f^{\widehat M}(\pi)]$ → $\mathbb E_{\pi\sim p}|f^M(\pi)-f^{\widehat M}(\pi)|$; reason: the absolute value bounds the signed difference, and the proof uses the absolute form (Steps 2–3, p. 110)
--   - generalization: $p=p_{\widehat M}$ → any probability distribution $p$ on decisions; reason: the notes' $p_{\widehat M}$ is one such distribution
--   - reading: the chain's final "$\le\varepsilon$" → omitted; reason: it is the constraint of (6.36) for the specific model chosen there, not a property of arbitrary models
--   - reading: expectations of $D_{\mathrm{TV}}$ and $D^2_{\mathrm H}$ → integrals with both maps assumed measurable; reason: the expectations presuppose measurability
--   - encoding: $\mathbb E_{\pi\sim p}D^2_{\mathrm H}$ → a Lebesgue integral in $[0,\infty]$, converted to a real number under the square root; reason: Lean convention; the integral is at most $2$, so nothing is lost
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, proof of Proposition 28, (6.40), p. 109

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_IsModel
import Definitions.Def_FoundationsRL_DECLower_meanReward
import Definitions.Def_FoundationsRL_DECLower_tvDist
import Definitions.Def_FoundationsRL_DECLower_hellingerSq

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **(6.40): mean rewards are controlled by TV and Hellinger distance.**
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, proof of Proposition 28, (6.40), p. 109: "since rewards are in [0, 1], we have
E_{π∼p_M̂}[f^M(π) − f^M̂(π)] ≤ E_{π∼p_M̂}[D_TV(M(π), M̂(π))] ≤ √(E_{π∼p_M̂}[D²_H(M(π), M̂(π))]) ≤ ε."

For models `M, M̂` (rewards in `[0, 1]`) and any probability measure `p` on decisions such that
`π ↦ D_TV(M(π), M̂(π))` and `π ↦ D²_H(M(π), M̂(π))` are measurable:
`E_p|f^M − f^M̂| ≤ E_p[D_TV(M(π), M̂(π))] ≤ √(E_p[D²_H(M(π), M̂(π))])`.

**Formalization Note.** The notes apply it to `p = p_M̂`; it is stated for any `p`. The first
link has `|f^M − f^M̂|` (the proof uses it in that form in Steps 2–3), which implies the printed
one. The final `≤ ε` is the constraint of (6.36), not part of the statement. The measurability
hypotheses are presupposed by the expectations. -/
theorem integral_abs_meanReward_sub_le {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (M Mhat : Kernel D (ℝ × O)) (hM : IsModel M) (hMhat : IsModel Mhat)
    (p : Measure D) [IsProbabilityMeasure p]
    (htv : Measurable (fun d => tvDist (M d) (Mhat d)))
    (hH : Measurable (fun d => hellingerSq (M d) (Mhat d))) :
    ∫ d, |meanReward M d - meanReward Mhat d| ∂p ≤ ∫ d, tvDist (M d) (Mhat d) ∂p ∧
      ∫ d, tvDist (M d) (Mhat d) ∂p
        ≤ Real.sqrt (∫⁻ d, hellingerSq (M d) (Mhat d) ∂p).toReal := by sorry

end FoundationsRL.DECLower
