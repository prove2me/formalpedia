-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_onsager_cancellation
-- name    : FreeProbAMP.StateEvolution.onsager_cancellation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:07.836028+00:00
-- url     : https://prove2.me/theorems/a0b60c95-5803-4bdb-89e4-a2efadbca860
-- title:
--   Lemma 6.6 — matrix-side Onsager cancellation
-- statement:
--   Assume the standing AMP setup, its recursively specified state law and the induction hypothesis $H_t$ for $1\le t\le T$. Form $Q_{t-1},R_{t-1},X_{t-1},G_{M,t-1},\beta_t,h^t,\delta_t$ exactly as in (6.4)–(6.8), with the derivative shift $(d_k^{(t)})_r=\mathbf1_{r<k}d_{k,r+1}$ for every $0\le r<t$. Then
--
--   $$\|X_{t-1}^*h^t-\alpha_dG_{M,t-1}\delta_t\|_{\mathbb R^t}\xrightarrow{\mathbb P}0,$$
--   $$\|R_{t-1}G_{M,t-1}^{-1}X_{t-1}^*h^t-\alpha_dR_{t-1}\delta_t\|_{\rm op}\xrightarrow{\mathbb P}0.$$
--
--   The coefficient-space norm is Euclidean, and the second error uses the matrix operator norm. This is the matrix-side cancellation statement; $H_t$ is not introduced as a hypothesis of either state-evolution theorem. No additive perturbation noise is part of the model.
--
--   Differences from the source:
--   - encoding: positive matrix dimension d tends to infinity → natural index j represents physical dimension j+1; reason: bijection with all positive dimensions; n(j) remains arbitrary
--   - encoding: the recursively specified Gaussian–semicircular limiting process → arbitrary probability/C*-space realizations satisfying precisely the state law; reason: finite Gaussian covariance and semicircular Fock realizations exist and have identical moments and faithful norms
--   - encoding: sample sizes n(d) with n(d) → ∞ → n(d) ≥ 1 for every d; reason: nondegeneracy only; at n = 0 the source's 1/n and n^{-1/2} normalizations are undefined, and n(d) → ∞ leaves only finitely many such d, which no limit statement sees
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 32, Lemma 6.6, (6.9)–(6.10); definitions (6.4)–(6.8), pp. 31–32

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Lemma 6.6, submission p.32; both (6.9) and (6.10). -/
theorem onsager_cancellation
    {Ω E B : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [CStarAlgebra B]
    (D : FiniteData Ω) (L : LimitData E B) (T t : ℕ) (α : ℝ)
    (ht : 1 ≤ t) (htT : t ≤ T)
    (hA : AMPAssumptions D L T α) (hL : StateLaw L T α D.a D.g)
    (hi : InductionHypothesis D L t) :
    InProb D.μ (fun d ω => euclid (cancellationVector D t d ω)) 0 ∧
    InProb D.μ (fun d ω => opNorm (cancellationMatrix D t d ω)) 0 := by sorry

end FreeProbAMP.StateEvolution
