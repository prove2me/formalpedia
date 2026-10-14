-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_appendix_b_19
-- name    : LookaheadAPI.LeastSquares.appendix_b_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:54:04.140834+00:00
-- url     : https://prove2.me/theorems/70b97970-a176-4a98-a22b-f0bf56118eb8
-- title:
--   Appendix B, eq. (19) — the error recursion $\delta_k\le\beta\delta_{k-1}+\tau$ for Algorithm 2
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\alpha)$ be a finite discounted MDP with rewards in $[0,1]$ and $0<\alpha<1$, let $H\ge1$, and let $(J_k,\mu_k,w_k,\theta_k)$ be a run of Algorithm 2 under Assumption 1, with $\mu_0$ any deterministic policy. Put $\delta_k=\|J_k-J^{\mu_k}\|_\infty$, and let
--   $$\beta=\alpha^{m+H-1}\delta_{FV},\qquad \tau=\frac{\alpha^m+\alpha^{m+H-1}}{1-\alpha}\,\delta_{FV}+\delta_{app}+\delta_{FV}\varepsilon_{PE}.$$
--   Then:
--
--   1. for every $k\ge1$, $\delta_k\le\beta\,\delta_{k-1}+\tau$;
--   2. iterating, for every $k\ge0$, $\displaystyle\delta_k\le\beta^k\delta_0+\sum_{i=0}^{k-1}\beta^i\tau$;
--   3. if $\beta<1$, then for every $k\ge0$, $$\delta_k\le\beta^k\delta_0+\frac{\tau}{1-\beta}. \tag{19}$$
--
--   This computes the parameters $\beta$ and $\mu=\tau/(1-\beta)$ with which Proposition 1 applies to Algorithm 2.
-- source:
--   arXiv:2109.13419v7, pp. 20–21, Appendix B (recursion for δ_k and eq. (19))

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

namespace LookaheadAPI.LeastSquares

/-- Appendix B, the recursion and (19) (pp. 20–21): for every run of Algorithm 2 under
Assumption 1 (with `μ_0` any deterministic policy), `δ_k := ‖J_k − J^{μ_k}‖_∞` satisfies
`δ_k ≤ β δ_{k−1} + τ` for `k ≥ 1`; iterating, `δ_k ≤ β^k δ_0 + ∑_{i=0}^{k−1} β^i τ`; and, when
`β < 1`, `δ_k ≤ β^k δ_0 + τ/(1 − β)`, where `β = α^{m+H−1}δ_FV` and
`τ = (α^m + α^{m+H−1})/(1−α) δ_FV + δ_app + δ_FV ε_PE`. -/
theorem appendix_b_19 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (hH : 1 ≤ H) (εLA εPE : ℝ)
    (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ)
    (hA1 : Assumption1 Φ D w εPE)
    (hrun : IsRunAlg2 M Φ D m H εLA J μ w θ) :
    (∀ k : ℕ, ‖J (k + 1) - valueOf M (μ (k + 1))‖ ≤
      betaLS M Φ D m H * ‖J k - valueOf M (μ k)‖ + tauLS M Φ D m H εPE) ∧
    (∀ k : ℕ, ‖J k - valueOf M (μ k)‖ ≤
      betaLS M Φ D m H ^ k * ‖J 0 - valueOf M (μ 0)‖ +
        ∑ i ∈ Finset.range k, betaLS M Φ D m H ^ i * tauLS M Φ D m H εPE) ∧
    (betaLS M Φ D m H < 1 → ∀ k : ℕ, ‖J k - valueOf M (μ k)‖ ≤
      betaLS M Φ D m H ^ k * ‖J 0 - valueOf M (μ 0)‖ +
        tauLS M Φ D m H εPE / (1 - betaLS M Φ D m H)) := by sorry

end LookaheadAPI.LeastSquares
