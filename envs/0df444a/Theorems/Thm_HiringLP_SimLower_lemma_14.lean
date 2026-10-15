-- Prove2me | Theorems.Thm_HiringLP_SimLower_lemma_14
-- name    : HiringLP.SimLower.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:36.226778+00:00
-- url     : https://prove2.me/theorems/89d1e7e1-d1ac-4256-a265-c4378363be5e
-- title:
--   Lemma 14 — if P_high > k, deflating p to Σ_{V_high} p′ = k does not increase the ratio R_{ALG^{s*}}/LP_sim
-- statement:
--   Let $\tau\in(0,1)$ and let $I=(k,n,p,v)$ be a valid $\tau$-bounded instance with
--   $$\sum_{i\in V_{\mathrm{high}}}p_i>k,$$
--   and assume moreover that $v_i\ne1$ for every $i$. Let $s^*\in[0,1]$ maximise $s\mapsto s-s/\tau+\mathbb E[\min\{\mathrm{Pois}(sk),k\}]/(\tau k)$ over $[0,1]$. Then there is a valid $\tau$-bounded instance $I'=(k,n,p',v)$ with the same $k$, $n$ and $v$ such that $\sum_{i\in V_{\mathrm{high}}}p'_i=k$ and, whenever $\mathrm{ALG}^{s^*}_{\mathrm{sim}}$ is run on an optimal solution of $\mathrm{LP}_{\mathrm{sim}}(I)$ for $I$ and on an optimal solution of $\mathrm{LP}_{\mathrm{sim}}(I')$ for $I'$,
--   $$\frac{R_{\mathrm{ALG}^{s^*}_{\mathrm{sim}}}(I)}{\mathrm{LP}_{\mathrm{sim}}(I)}\ \ge\ \frac{R_{\mathrm{ALG}^{s^*}_{\mathrm{sim}}}(I')}{\mathrm{LP}_{\mathrm{sim}}(I')}.$$
--
--   It reduces the case $P_{\mathrm{high}}>k$ of the main theorem to the boundary case $P_{\mathrm{high}}=k$ covered by Lemma 13.
--
--   **Formalization Note** The hypothesis $v_i\ne1$ is an addition: with a candidate of value exactly $1$ the optimal LP mass is not unique, and the inequality can fail when the two runs use differently sized optimal solutions. Under it the optimal mass is unique, so the ratios do not depend on the choice. Both LP values are positive here, so the divisions are genuine. $s^*$ is read as a maximiser of the $\alpha^\tau_k$ objective over $[0,1]$ (the paper: "parameter $s$ can be optimized … we let $s^*$ denote the optimal value"); it depends only on $k$ and $\tau$, which $I$ and $I'$ share.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 29, Lemma 14

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model
import Definitions.Def_HiringLP_SimLower_LP
import Definitions.Def_HiringLP_SimLower_Algorithm
import Definitions.Def_HiringLP_SimLower_PoissonRatio

open Finset

namespace HiringLP.SimLower

/-- Lemma 14 (p. 29), under the disclosed hypothesis `vᵢ ≠ 1` for all `i`: if `P_high > k`, there is a
τ-bounded instance `I′ = (k, n, p′, v)` with `Σ_{i ∈ V_high} p′ᵢ = k` such that
`R_{ALG^{s*}}(I′)/LP_sim(I′) ≤ R_{ALG^{s*}}(I)/LP_sim(I)`, where `s*` maximises the `α^τ_k` objective over
`[0, 1]` and each run uses an optimal solution of its own LP. -/
theorem lemma_14 {n : ℕ} (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (I : SimInstance n) (hI : I.Valid) (hτ : I.TauBounded τ) (hne1 : ∀ i, I.v i ≠ 1)
    (hhigh : (I.k : ℝ) < Phigh I)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hsmax : ∀ s' ∈ Set.Icc (0 : ℝ) 1, ratioObj I.k τ s' ≤ ratioObj I.k τ s) :
    ∃ I' : SimInstance n, I'.k = I.k ∧ I'.v = I.v ∧ I'.Valid ∧ I'.TauBounded τ ∧
      ∑ i ∈ Vhigh I', I'.p i = I.k ∧
      ∀ (y : Fin n → ℝ) (z : ℝ) (y' : Fin n → ℝ) (z' : ℝ), IsLPOpt I y z → IsLPOpt I' y' z' →
        algReward I' y' s / LPsim I' ≤ algReward I y s / LPsim I := by sorry

end HiringLP.SimLower
