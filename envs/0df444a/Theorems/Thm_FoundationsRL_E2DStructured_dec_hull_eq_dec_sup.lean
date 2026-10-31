-- Prove2me | Theorems.Thm_FoundationsRL_E2DStructured_dec_hull_eq_dec_sup
-- name    : FoundationsRL.E2DStructured.dec_hull_eq_dec_sup
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:11.01702+00:00
-- url     : https://prove2.me/theorems/38afeb71-2976-49d0-86c7-556233273253
-- title:
--   Proposition 24 (corrected: $\Pi$ finite or $\mathcal F$ finite and bounded) — reference models outside $\mathrm{co}(\mathcal F)$ do not raise the DEC
-- statement:
--   Let $\mathcal F$ be a nonempty class of reward functions on $\Pi$ and $\gamma>0$. If $\Pi$ is finite, or $\mathcal F$ is a finite class of bounded functions, then
--   $$\sup_{\hat f:\Pi\to\mathbb R}\mathrm{dec}_\gamma(\mathcal F,\hat f)=\sup_{\hat f\in\mathrm{co}(\mathcal F)}\mathrm{dec}_\gamma(\mathcal F,\hat f).$$
--
--   The value of the Decision-Estimation Coefficient therefore cannot be increased by taking reference models outside the convex hull of $\mathcal F$. This is what turns the regret bound over unconstrained estimates into a bound in terms of $\mathrm{dec}_\gamma(\mathcal F)$.
--
--   Differences from the source:
--   - correction: the identity for arbitrary Π and F → the identity when Π is finite or F is a finite class of bounded functions; reason: the printed statement is false: for Π = ℕ, f_i(π) = I{π ≥ i}, γ ≥ 1, the left side is at least 1 and the right side at most 0; the minimax theorem of Exercise 10 needs a compact player and a real game
--   - encoding: min and max in the DEC → inf and sup in EReal; reason: (4.19) reads them this way
--   - encoding: real expectations → Lebesgue integrals in [0, ∞] subtracted in EReal; the undefined case ∞ − ∞ is scored −∞; reason: the integrand may be non-integrable for unbounded functions, where a Bochner integral would return 0
--   - encoding: f̂ : Π → ℝ; f : Π → ℝ, π_f = arg max f → measurable f̂; every f ∈ F measurable with a maximizer; F nonempty; reason: the expectations and π_f are defined only then, and F ∋ f⋆ is nonempty by Assumption 5 (p. 57); for empty Π and F the two sides would be +∞ and −∞
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 24, p. 80; Exercise 10, p. 80

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_IsRewardClass
import Definitions.Def_FoundationsRL_E2DStructured_HasFiniteGame
import Definitions.Def_FoundationsRL_E2DStructured_decHull
import Definitions.Def_FoundationsRL_E2DStructured_decSup

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- **Proposition 24** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.6, p. 80), corrected: if `Π` is finite or `F` is a finite class of
bounded functions, `sup_{f̂:Π→ℝ} dec_γ(F, f̂) = sup_{f̂∈co(F)} dec_γ(F, f̂)`.

**Formalization Note.** As printed, without `HasFiniteGame`, the identity is false: for `Π = ℕ` and
`f_i(π) = I{π ≥ i}`, the left side is at least `1` and for `γ ≥ 1` the right side is at most `0`. -/
theorem dec_hull_eq_dec_sup {D : Type*} [MeasurableSpace D] (F : Set (D → ℝ))
    (hF : IsRewardClass F) (hne : F.Nonempty) (hfin : HasFiniteGame F) (γ : ℝ) (hγ : 0 < γ) :
    decSup γ F = decHull γ F := by sorry

end FoundationsRL.E2DStructured
