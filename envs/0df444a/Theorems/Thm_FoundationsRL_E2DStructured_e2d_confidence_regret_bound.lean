-- Prove2me | Theorems.Thm_FoundationsRL_E2DStructured_e2d_confidence_regret_bound
-- name    : FoundationsRL.E2DStructured.e2d_confidence_regret_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:27.283962+00:00
-- url     : https://prove2.me/theorems/2c32cc7a-3941-4cf3-8c37-0f4a6fd602b5
-- title:
--   Proposition 19 (corrected: sup over all $\hat f$; $\mathrm{dec}_\gamma(\mathcal F^t)$ when $\Pi$ or $\mathcal F$ is finite) — E2D with confidence sets
-- statement:
--   Consider E2D with confidence sets: at round $t$ the algorithm forms
--   $$\mathcal F^t=\Big\{f\in\mathcal F:\ \sum_{i<t}\mathbb E_{\pi^i\sim p^i}\big[(\hat f^i(\pi^i)-f(\pi^i))^2\big]\le\beta\Big\}$$
--   and plays a distribution $p^t$ solving the DEC minimax problem with the adversary restricted to $\mathcal F^t$. Let $\delta\in(0,1)$, $\gamma>0$ and $\beta=\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta)$. If the oracle satisfies Definition 7 then the following hold.
--
--   1. With probability at least $1-\delta$,
--   $$\mathrm{Reg}\le\sum_{t=1}^T\sup_{\hat f:\Pi\to\mathbb R}\mathrm{dec}_\gamma(\mathcal F^t,\hat f)+\gamma\cdot\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta).$$
--   2. If $\Pi$ is finite, or $\mathcal F$ is a finite class of bounded functions, then with probability at least $1-\delta$,
--   $$\mathrm{Reg}\le\sum_{t=1}^T\mathrm{dec}_\gamma(\mathcal F^t)+\gamma\cdot\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta).$$
--
--   The bound can improve on Proposition 13 when the confidence sets shrink quickly.
--
--   Differences from the source:
--   - correction: Reg ≤ Σ_t dec_γ(F^t) + γ·EstSq with dec_γ(F^t) the supremum over co(F^t), for arbitrary Π and F → conjunct 1 has the supremum over all measurable f̂ for arbitrary Π and F; conjunct 2 is (4.26) when Π is finite or F is a finite class of bounded functions; reason: the printed statement is false by the example of Proposition 13: take β = 1/2 and p^t = δ_1, so that F^t ⊇ {f_i : i ≥ 2}, dec_γ(F^t, 0) = 1, δ_1 is a minimizer, Reg = T and dec_γ(F^t) ≤ 0 for γ ≥ 1, so the right side is at most γ/2 < T for T > γ ≥ 1
--   - reading: F^t is defined with f⋆ in the summand, a condition independent of f → F^t is defined with f in the summand; reason: the printed set is F or ∅; the construction is the online-to-confidence-set conversion of footnote 13, and this reading gives smaller sets, hence the stronger bound
--   - encoding: min and max in the DEC and arg min in E2D → inf and sup, with the E2D distribution assumed to attain the infimum; reason: (4.19) reads them this way; if the infimum is not attained the algorithm of p. 64 is not defined
--   - encoding: real expectations → Lebesgue integrals in [0, ∞] subtracted in EReal; the undefined case ∞ − ∞ is scored −∞; reason: the integrand may be non-integrable for unbounded functions, where a Bochner integral would return 0
--   - encoding: f : Π → ℝ and f̂ : Π → ℝ, π_f = arg max f → every f ∈ F measurable with a maximizer, every f̂^t measurable, and the supremum over f̂ restricted to measurable functions; reason: the expectations and π_f in the statement are defined only then
--   - encoding: rounds t = 1, …, T → rounds 0, …, T − 1; EstSq a real number; reason: Lean convention, same instances
--   - generalization: decisions π^t ∼ p^t adaptive to the history, rewards with E[r|π] = f⋆(π), oracle output as in Definition 7 → arbitrary processes p^t, f̂^t on a probability space satisfying the E2D rule and the oracle bound; reason: no other property of the protocol is used; the protocol of the notes is a special case
--   - generalization: confidence radius β > 0 (input of the algorithm, p. 75) → β = est any real number; reason: the proof does not use β > 0; the case est > 0 is the source's
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 19, (4.26), p. 76; E2D with confidence sets, p. 75

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_IsRewardClass
import Definitions.Def_FoundationsRL_E2DStructured_HasFiniteGame
import Definitions.Def_FoundationsRL_E2DStructured_decHull
import Definitions.Def_FoundationsRL_E2DStructured_decSup
import Definitions.Def_FoundationsRL_E2DStructured_IsE2DChoice
import Definitions.Def_FoundationsRL_E2DStructured_regret
import Definitions.Def_FoundationsRL_E2DStructured_OnlineRegressionGuarantee
import Definitions.Def_FoundationsRL_E2DStructured_confidenceSet

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- **Proposition 19** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.4.1, p. 76, (4.26)), corrected: E2D with confidence sets of radius
`β = EstSq(F, T, δ)` has, with probability at least `1 − δ`,
`Reg ≤ ∑_{t=1}^T sup_{f̂:Π→ℝ} dec_γ(F^t, f̂) + γ·EstSq(F, T, δ)`, and if `Π` is finite or `F` is a
finite class of bounded functions, `Reg ≤ ∑_{t=1}^T dec_γ(F^t) + γ·EstSq(F, T, δ)`, which is (4.26).

**Formalization Note.** The two conjuncts mirror `e2d_regret_bound`, with the same counterexample to
(4.26) for infinite `Π` and `F`. Each `p t ω` solves the minimax problem over `F^t`, which is built
from the earlier rounds of the same outcome `ω`. -/
theorem e2d_confidence_regret_bound {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Set (D → ℝ)) (hF : IsRewardClass F)
    (fstar : D → ℝ) (hfstar : fstar ∈ F) (γ : ℝ) (hγ : 0 < γ) (T : ℕ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (est : ℝ)
    (p : ℕ → Ω → ProbabilityMeasure D) (fhat : ℕ → Ω → D → ℝ)
    (hfhat : ∀ t < T, ∀ ω, Measurable (fhat t ω))
    (hE2D : ∀ t < T, ∀ ω, IsE2DChoice γ
      (confidenceSet F est t (fun i => p i ω) (fun i => fhat i ω)) (fhat t ω) (p t ω))
    (horacle : OnlineRegressionGuarantee P T δ est p fhat fstar) :
    ENNReal.ofReal (1 - δ) ≤ P {ω | ((regret T fstar (fun t => p t ω) : ℝ≥0∞) : EReal) ≤
        ∑ t ∈ Finset.range T,
          decSup γ (confidenceSet F est t (fun i => p i ω) (fun i => fhat i ω)) +
          (γ : EReal) * (est : EReal)} ∧
    (HasFiniteGame F → ENNReal.ofReal (1 - δ) ≤ P {ω | ((regret T fstar (fun t => p t ω) : ℝ≥0∞) : EReal) ≤
        ∑ t ∈ Finset.range T,
          decHull γ (confidenceSet F est t (fun i => p i ω) (fun i => fhat i ω)) +
          (γ : EReal) * (est : EReal)}) := by sorry

end FoundationsRL.E2DStructured
