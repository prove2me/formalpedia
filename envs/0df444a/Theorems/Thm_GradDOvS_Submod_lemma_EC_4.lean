-- Prove2me | Theorems.Thm_GradDOvS_Submod_lemma_EC_4
-- name    : GradDOvS.Submod.lemma_EC_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:18:04.475619+00:00
-- url     : https://prove2.me/theorems/5d901f70-d5a5-4254-bdf1-9e0d70c06da6
-- title:
--   Lemma EC.4, p. ec6 (PDF 44) — projected steps with η = 1/(M√T) have average regret at most dM/√T
-- statement:
--   Let $M > 0$, $T \ge 1$ and $\eta = 1/(M\sqrt T)$. Let $\tilde g^0,\dots,\tilde g^{T-1} \in \mathbb R^d$ satisfy $|\tilde g^t_i| \le M$ for all $i$, let $x^0 \in [0,1]^d$ and $x^{t+1} = P_X(x^t - \eta \tilde g^t)$ for $t < T$, where $P_X$ is the projection onto $[0,1]^d$. Then for every $x^* \in [0,1]^d$
--   $$\frac1T \sum_{t=0}^{T-1} \langle \tilde g^t, x^t - x^*\rangle \le \frac{dM}{\sqrt T}.$$
--
--   This is the deterministic optimization part of the analysis of Algorithm 2.
--
--   **Formalization Note** The page states the bound for the iterates of Algorithm 2 and a minimizer $x^*$ of $f$; the proof uses only that the truncated vectors are bounded by $M$ and that $x^0, x^*$ lie in $[0,1]^d$, and that is how it is stated here (a stronger statement).
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. ec6 (PDF 44), Lemma EC.4

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Lemma EC.4, p. ec6 (PDF 44): projected steps `x^{t+1} = P_X(x^t - η g̃^t)` with step size
`η = 1/(M√T)` and vectors `|g̃^t_i| ≤ M`, started in `[0,1]^d`, satisfy
`(1/T) ∑_{t<T} ⟨g̃^t, x^t - x*⟩ ≤ d M/√T` for every `x* ∈ [0,1]^d`. -/
theorem lemma_EC_4 {d : ℕ} (T : ℕ) (hT : 1 ≤ T) (M : ℝ) (hM : 0 < M) (g x : ℕ → Fin d → ℝ)
    (hg : ∀ t < T, ∀ i, |g t i| ≤ M) (hx0 : x 0 ∈ box d)
    (hstep : ∀ t < T, x (t + 1) = proj (x t - (1 / (M * Real.sqrt T)) • g t))
    (xstar : Fin d → ℝ) (hxstar : xstar ∈ box d) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ i, g t i * (x t i - xstar i) ≤ d * M / Real.sqrt T
    := by sorry

end GradDOvS.Submod
