-- Prove2me | Theorems.Thm_FoundationsRL_E2DStructured_contextual_e2d_regret_bound
-- name    : FoundationsRL.E2DStructured.contextual_e2d_regret_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:48.336169+00:00
-- url     : https://prove2.me/theorems/86afb600-7fd4-4e37-b7b1-2a41df9abb06
-- title:
--   Proposition 23 (corrected: sup over all $\hat f$; $\mathrm{dec}_\gamma(\mathcal F(x,\cdot))$ when $\Pi$ or $\mathcal F(x,\cdot)$ is finite) — contextual E2D
-- statement:
--   Consider contextual structured bandits with contexts $x^t\in\mathcal X$, chosen in an arbitrary way, a class $\mathcal F$ of functions $f:\mathcal X\times\Pi\to\mathbb R$ containing the true mean reward $f^\star$, and $\pi_f(x)\in\arg\max_\pi f(x,\pi)$. At round $t$ contextual E2D obtains an estimate $\hat f^t$ and plays a distribution $p^t$ solving the DEC minimax problem for the projection $\mathcal F(x^t,\cdot)$ and the reference model $\hat f^t(x^t,\cdot)$. Let $\gamma>0$ and $\delta\in\mathbb R$, and suppose the oracle satisfies, with probability at least $1-\delta$, $\sum_{t=1}^T\mathbb E_{\pi^t\sim p^t}(\hat f^t(x^t,\pi^t)-f^\star(x^t,\pi^t))^2\le\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta)$. Then the following hold, with $\mathrm{Reg}=\sum_{t=1}^T\mathbb E_{\pi^t\sim p^t}[f^\star(x^t,\pi_{f^\star}(x^t))-f^\star(x^t,\pi^t)]$.
--
--   1. With probability at least $1-\delta$,
--   $$\mathrm{Reg}\le\sup_{x\in\mathcal X}\sup_{\hat f:\Pi\to\mathbb R}\mathrm{dec}_\gamma(\mathcal F(x,\cdot),\hat f)\cdot T+\gamma\cdot\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta).$$
--   2. If for every $x$ the space $\Pi$ is finite or $\mathcal F(x,\cdot)$ is a finite class of bounded functions, then with probability at least $1-\delta$,
--   $$\mathrm{Reg}\le\sup_{x\in\mathcal X}\mathrm{dec}_\gamma(\mathcal F(x,\cdot))\cdot T+\gamma\cdot\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta).$$
--
--   Whenever the DEC is bounded for all projections, contextual E2D has low regret; this generalizes the SquareCB method to large action spaces.
--
--   Differences from the source:
--   - correction: Reg ≤ sup_x dec_γ(F(x, ·))·T + γ·EstSq with dec_γ the supremum over co(F(x, ·)), for arbitrary Π and F → conjunct 1 has the supremum over all measurable f̂ for arbitrary Π and F; conjunct 2 is (4.30) when for each x, Π is finite or F(x, ·) is a finite class of bounded functions; reason: the printed statement is false: a one-point context space reduces it to (4.17), and the example of Proposition 13 applies
--   - reading: (4.30) has no probability quantifier and leaves T and δ implicit → with probability at least 1 − δ; reason: the oracle bound on p. 78 holds only with that probability, and Proposition 13 is stated this way
--   - encoding: min and max in the DEC and arg min in E2D → inf and sup, with the E2D distribution assumed to attain the infimum; reason: (4.19) reads them this way; if the infimum is not attained the algorithm of p. 64 is not defined
--   - encoding: real expectations → Lebesgue integrals in [0, ∞] subtracted in EReal; the undefined case ∞ − ∞ is scored −∞; reason: the integrand may be non-integrable for unbounded functions, where a Bochner integral would return 0
--   - encoding: f(x, ·) : Π → ℝ, π_f(x) = arg max; f̂^t : X × Π → ℝ → every f(x, ·) measurable with a maximizer, f̂^t(x^t, ·) measurable, and the supremum over f̂ restricted to measurable functions; reason: the expectations and π_f(x) in the statement are defined only then
--   - encoding: rounds t = 1, …, T; EstSq → rounds 0, …, T − 1; EstSq a real number; reason: Lean convention, same instances
--   - generalization: contexts generated arbitrarily, decisions adaptive to the history, oracle output from the observed data → arbitrary processes x^t, p^t, f̂^t on a probability space satisfying the E2D rule and the oracle bound; reason: no other property of the protocol is used; the protocol of the notes is a special case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 23, (4.30), p. 79; protocol and oracle, p. 78

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_IsRewardClass
import Definitions.Def_FoundationsRL_E2DStructured_HasFiniteGame
import Definitions.Def_FoundationsRL_E2DStructured_decHull
import Definitions.Def_FoundationsRL_E2DStructured_decSup
import Definitions.Def_FoundationsRL_E2DStructured_IsE2DChoice
import Definitions.Def_FoundationsRL_E2DStructured_expectedGap
import Definitions.Def_FoundationsRL_E2DStructured_sectionClass
import Definitions.Def_FoundationsRL_E2DStructured_ContextualOnlineRegressionGuarantee

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- **Proposition 23** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.5, p. 79, (4.30)), corrected: contextual E2D has, with probability at
least `1 − δ`, `Reg ≤ sup_{x∈X} sup_{f̂:Π→ℝ} dec_γ(F(x, ·), f̂) · T + γ·EstSq(F, T, δ)`, and if for every
context `Π` is finite or `F(x, ·)` is a finite class of bounded functions,
`Reg ≤ sup_{x∈X} dec_γ(F(x, ·)) · T + γ·EstSq(F, T, δ)`, which is (4.30).

**Formalization Note.** The print omits the probability quantifier; it is read as in Proposition 13,
as the oracle guarantee on p. 78 requires. Contexts `x t ω` are arbitrary. `E_{π∼p^t}` of the regret at
context `x^t` is `expectedGap (fstar (x t ω)) (p t ω)`. A singleton context space gives
`e2d_regret_bound`, so the counterexample to Proposition 13 applies to (4.30) as printed. -/
theorem contextual_e2d_regret_bound {X D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Set (X → D → ℝ))
    (hF : ∀ x, IsRewardClass (sectionClass F x))
    (fstar : X → D → ℝ) (hfstar : fstar ∈ F) (γ : ℝ) (hγ : 0 < γ) (T : ℕ) (δ est : ℝ)
    (x : ℕ → Ω → X) (p : ℕ → Ω → ProbabilityMeasure D) (fhat : ℕ → Ω → X → D → ℝ)
    (hfhat : ∀ t < T, ∀ ω, Measurable (fhat t ω (x t ω)))
    (hE2D : ∀ t < T, ∀ ω, IsE2DChoice γ (sectionClass F (x t ω)) (fhat t ω (x t ω)) (p t ω))
    (horacle : ContextualOnlineRegressionGuarantee P T δ est x p fhat fstar) :
    ENNReal.ofReal (1 - δ) ≤ P {ω |
        ((∑ t ∈ Finset.range T, expectedGap (fstar (x t ω)) (p t ω) : ℝ≥0∞) : EReal) ≤
          (⨆ c : X, decSup γ (sectionClass F c)) * (T : EReal) + (γ : EReal) * (est : EReal)} ∧
    ((∀ c, HasFiniteGame (sectionClass F c)) → ENNReal.ofReal (1 - δ) ≤ P {ω |
        ((∑ t ∈ Finset.range T, expectedGap (fstar (x t ω)) (p t ω) : ℝ≥0∞) : EReal) ≤
          (⨆ c : X, decHull γ (sectionClass F c)) * (T : EReal) + (γ : EReal) * (est : EReal)}) := by sorry

end FoundationsRL.E2DStructured
