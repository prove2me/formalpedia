-- Prove2me | Theorems.Thm_FoundationsRL_E2DStructured_e2d_regret_bound
-- name    : FoundationsRL.E2DStructured.e2d_regret_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:35.066829+00:00
-- url     : https://prove2.me/theorems/c617c432-5cd5-4280-b1c8-aa8a76554934
-- title:
--   Proposition 13 (corrected: sup over all $\hat f$; $\mathrm{co}(\mathcal F)$ when $\Pi$ or $\mathcal F$ is finite) — E2D regret $\le\mathrm{dec}_\gamma\cdot T+\gamma\cdot\mathrm{Est}_{\mathsf{Sq}}$
-- statement:
--   This is the regret bound of the Estimation-to-Decisions algorithm, Proposition 13 of the notes (Foster et al.).
--
--   Let $\Pi$ be a measurable decision space and $\mathcal F$ a class of reward functions on $\Pi$ containing the true mean reward $f^\star$. Let $\gamma>0$ and $\delta\in\mathbb R$. At each round E2D obtains an estimate $\hat f^t$ from an online regression oracle and plays a distribution $p^t$ solving
--   $$\min_{p\in\Delta(\Pi)}\max_{f\in\mathcal F}\mathbb E_{\pi\sim p}\big[f(\pi_f)-f(\pi)-\gamma\,(f(\pi)-\hat f^t(\pi))^2\big].$$
--   If the oracle satisfies Definition 7 with error bound $\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta)$, then the following hold.
--
--   1. With probability at least $1-\delta$,
--   $$\mathrm{Reg}\le\sup_{\hat f:\Pi\to\mathbb R}\mathrm{dec}_\gamma(\mathcal F,\hat f)\cdot T+\gamma\cdot\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta).$$
--   2. If $\Pi$ is finite, or $\mathcal F$ is a finite class of bounded functions, then with probability at least $1-\delta$,
--   $$\mathrm{Reg}\le\mathrm{dec}_\gamma(\mathcal F)\cdot T+\gamma\cdot\mathrm{Est}_{\mathsf{Sq}}(\mathcal F,T,\delta).$$
--
--   The bound separates the two sources of complexity in structured bandits: the difficulty of exploration, captured by the DEC, and the difficulty of estimation, captured by $\mathrm{Est}_{\mathsf{Sq}}$.
--
--   **Formalization Note** The estimates $\hat f^t$ need not lie in $\mathrm{co}(\mathcal F)$. The probability of the event is read with the outer measure when the event is not measurable. Regret and the DEC are compared in the extended reals.
--
--   Differences from the source:
--   - correction: Reg ≤ dec_γ(F)·T + γ·EstSq with dec_γ(F) the supremum over co(F), for arbitrary Π and F → conjunct 1 has the supremum over all measurable f̂ for arbitrary Π and F; conjunct 2 is (4.17) when Π is finite or F is a finite class of bounded functions; reason: the printed statement is false: Π = ℕ, F = {f_i : i ≥ 1}, f_i(π) = I{π ≥ i}, each f_i attaining its maximum: for f̂ ≡ 0 every p has inner value 1, so dec_γ(F, 0) = 1 and δ_1 is a minimizer, while for f̂ = Σ_{j≤N} λ_j f_j playing π = N gives value at most 0 when γ ≥ 1, so dec_γ(F) ≤ 0; with f⋆ = f_2, deterministic rewards and an oracle returning 0, E2D may play δ_1 forever, the estimation error is 0 and Reg = T > γ·EstSq for EstSq = 1, T > γ ≥ 1; conjunct 1 is the last display of the proof on p. 66; boundedness in the finite-F branch keeps the game real-valued, as Lemma 41 requires
--   - encoding: min and max in the DEC and arg min in E2D → inf and sup, with the E2D distribution assumed to attain the infimum; reason: (4.19) reads them this way; if the infimum is not attained the algorithm of p. 64 is not defined
--   - encoding: real expectations → Lebesgue integrals in [0, ∞] subtracted in EReal; the undefined case ∞ − ∞ is scored −∞; reason: the integrand may be non-integrable for unbounded functions, where a Bochner integral would return 0
--   - encoding: f : Π → ℝ and f̂ : Π → ℝ, π_f = arg max f → every f ∈ F measurable with a maximizer, every f̂^t measurable, and the supremum over f̂ restricted to measurable functions; reason: the expectations and π_f in the statement are defined only then
--   - encoding: rounds t = 1, …, T → rounds 0, …, T − 1; EstSq a real number; reason: Lean convention, same instances
--   - generalization: decisions π^t ∼ p^t adaptive to the history, rewards with E[r|π] = f⋆(π), oracle output as in Definition 7 → arbitrary processes p^t, f̂^t on a probability space satisfying the E2D rule and the oracle bound; reason: no other property of the protocol is used; the protocol of the notes is a special case
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Proposition 13, (4.17), p. 65; proof, p. 66

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_IsRewardClass
import Definitions.Def_FoundationsRL_E2DStructured_HasFiniteGame
import Definitions.Def_FoundationsRL_E2DStructured_decHull
import Definitions.Def_FoundationsRL_E2DStructured_decSup
import Definitions.Def_FoundationsRL_E2DStructured_IsE2DChoice
import Definitions.Def_FoundationsRL_E2DStructured_regret
import Definitions.Def_FoundationsRL_E2DStructured_OnlineRegressionGuarantee

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- **Proposition 13** (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 65, (4.17)), corrected: the E2D algorithm with exploration
parameter `γ > 0` guarantees, with probability at least `1 − δ`,
`Reg ≤ sup_{f̂:Π→ℝ} dec_γ(F, f̂) · T + γ·EstSq(F, T, δ)` for arbitrary `Π` and `F`, and if `Π` is finite
or `F` is a finite class of bounded functions, `Reg ≤ dec_γ(F) · T + γ·EstSq(F, T, δ)`, which is (4.17).

**Formalization Note.** The first conjunct is the last display of the proof on p. 66. As printed for
infinite `Π` and `F`, (4.17) is false (`Π = ℕ`, `f_i(π) = I{π ≥ i}`, `f⋆ = f_2`; see the item's list of
differences). `hE2D` says that `p t ω` solves the minimax problem of E2D against the estimate of the
same round; if the infimum in (4.15) is not attained there is no such `p`, and the algorithm is not
defined. The estimates need not lie in `co(F)`. The processes `p`, `fhat` are arbitrary, so the
statement covers the adaptive protocol of Definition 7. No range is imposed on `δ`, as
Definition 7 imposes none; for `δ ≥ 1` the claim is trivial. -/
theorem e2d_regret_bound {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Set (D → ℝ)) (hF : IsRewardClass F)
    (fstar : D → ℝ) (hfstar : fstar ∈ F) (γ : ℝ) (hγ : 0 < γ) (T : ℕ) (δ est : ℝ)
    (p : ℕ → Ω → ProbabilityMeasure D) (fhat : ℕ → Ω → D → ℝ)
    (hfhat : ∀ t < T, ∀ ω, Measurable (fhat t ω))
    (hE2D : ∀ t < T, ∀ ω, IsE2DChoice γ F (fhat t ω) (p t ω))
    (horacle : OnlineRegressionGuarantee P T δ est p fhat fstar) :
    ENNReal.ofReal (1 - δ) ≤ P {ω | ((regret T fstar (fun t => p t ω) : ℝ≥0∞) : EReal) ≤
        decSup γ F * (T : EReal) + (γ : EReal) * (est : EReal)} ∧
    (HasFiniteGame F → ENNReal.ofReal (1 - δ) ≤ P {ω | ((regret T fstar (fun t => p t ω) : ℝ≥0∞) : EReal) ≤
        decHull γ F * (T : EReal) + (γ : EReal) * (est : EReal)}) := by sorry

end FoundationsRL.E2DStructured
