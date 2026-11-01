-- Prove2me | Theorems.Thm_OfflineToOnline_lemma_2
-- name    : OfflineToOnline.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:33.77484+00:00
-- url     : https://prove2.me/theorems/4dde500a-301d-41e0-983b-0fdfa93e04cc
-- title:
--   Lemma 2 (corrected: $B$ bounds $R(u)-R(v)$ on $K$) — FTRL regret $O(CB^{1/2}\mu^{-1/2}T^{-1/2})$
-- statement:
--   There is an absolute constant $c$ with the following property. Let $K$ be a nonempty convex compact subset of a real normed space $E$, let $R:E\to\mathbb R$ be $\mu$-strongly convex on $K$ with respect to the norm ($\mu>0$), and let $B>0$ satisfy $R(u)-R(v)\le B$ for all $u,v\in K$. Let $C>0$, $T\ge1$, and let $l_1,\dots,l_T$ be linear losses with dual norms $\|l_t\|_*\le C$. If $w_1,\dots,w_T$ is a run of Follow-the-Regularized-Leader on $K$ with regularizer $R/\eta$, $\eta=\sqrt{\mu B/T}/C$, i.e. $w_t\in\arg\min_{w\in K}\sum_{s<t}l_s(w)+R(w)/\eta$, then
--
--   $$
--   \frac1T\Big(\sum_{t=1}^T\langle l_t,w_t\rangle-\min_{w\in K}\sum_{t=1}^T\langle l_t,w\rangle\Big)\ \le\ c\,C\,B^{1/2}\mu^{-1/2}T^{-1/2}.
--   $$
--
--   This is the regret bound of the online linear optimization step in the proof of Theorem 1; the dimension enters only through the strong convexity modulus $\mu$ and the range $B$ of the regularizer.
--
--   Differences from the source:
--   - correction: B > 0 upper bounds the function R → R(u) − R(v) ≤ B for all u, v ∈ K; reason: as printed the lemma is false: K = [−1,1], R(w) = w²/2 − 1/2 ≤ 0 < B, T = 1, l₁ = 1 gives regret 1 while the bound tends to 0 with B
--   - reading: Follow-the-Regularized-Leader with regularizer R (learning rate unspecified) → FTRL with regularizer R/η, η = √(μB/T)/C (OnlineLearningOCO.FoReL.IsFoReLRun, every tie-breaking rule); reason: the tuned rate is what produces the stated bound
--   - reading: O(C B^{1/2} μ^{−1/2} T^{−1/2}) → c · C · √B · μ^{−1/2} · T^{−1/2} with one c chosen before every parameter; reason: the strongest reading of O(·)
--   - generalization: R : ℝ^d → ℝ μ-strongly convex on ℝ^d (differentiable, footnote 23), K ⊆ ℝ^d → R μ-strongly convex on K only (Mathlib's StrongConvexOn), K in any real normed space; reason: differentiable strongly convex functions on ℝ^d with any norm satisfy the hypothesis
--   - encoding: loss vectors l_t with dual norm ‖l‖∗; min over K; rounds 1..T → continuous linear functionals with operator norm ‖l_t‖; sInf of the image of the compact K; K nonempty; reason: the operator norm is the dual norm of footnote 24; the minimum exists
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Lemma 2, p.47, with footnote 24

import Mathlib
import Definitions.Def_OnlineLearningOCO_FoReL_IsFoReLRun

universe u

namespace OfflineToOnline

/-- **Lemma 2** (Shalev-Shwartz 2012; corrected: `B` bounds `R(u) − R(v)` on `K`). There is an
absolute constant `c` such that: for an OLO problem on a convex compact nonempty decision set `K` in
a real normed space, Follow-the-Regularized-Leader with a regularizer `R` that is `μ`-strongly convex
on `K` with respect to the norm (`μ > 0`), with `R(u) − R(v) ≤ B` for `u, v ∈ K` (`B > 0`), and with
linear losses `l_t` whose dual norms are at most `C > 0`, run with learning rate
`η = √(μB/T)/C`, satisfies
`(1/T)(∑_{t=1}^T ⟨l_t, w_t⟩ − min_{w ∈ K} ∑_{t=1}^T ⟨l_t, w⟩) ≤ c · C B^{1/2} μ^{−1/2} T^{−1/2}`.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Lemma 2, p.47, with footnote 24 (dual norm).

Formalization Note: the page says "B > 0 upper bounds the function R"; that is false (`K = [−1, 1]`,
`R(w) = w²/2 − 1/2 ≤ 0`, `T = 1`, `l_1 = 1`: the regret is `1` while the bound tends to `0` with
`B`), and is corrected to a bound on the range of `R` over `K`. The learning rate the page leaves
unspecified is `η = √(μB/T)/C`, i.e. FTRL with regularizer `R/η`
(`OnlineLearningOCO.FoReL.IsFoReLRun`, 1-based rounds, every tie-breaking rule). The loss vector
`l_t` is a continuous linear functional and `‖l_t‖` its dual (operator) norm. `StrongConvexOn K μ R`
is Mathlib's: `R(a u + b v) ≤ a R(u) + b R(v) − a b (μ/2) ‖u − v‖²`. The O(·) is one absolute `c`,
chosen before everything else. The minimum over the compact `K` is written as `sInf`. -/
theorem lemma_2 : ∃ c : ℝ, ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E),
    Convex ℝ K → IsCompact K → K.Nonempty →
    ∀ μ : ℝ, 0 < μ → ∀ R : E → ℝ, StrongConvexOn K μ R →
    ∀ B : ℝ, 0 < B → (∀ u ∈ K, ∀ v ∈ K, R u - R v ≤ B) →
    ∀ C : ℝ, 0 < C → ∀ T : ℕ, 1 ≤ T →
    ∀ l : ℕ → E →L[ℝ] ℝ, (∀ t ∈ Finset.Icc 1 T, ‖l t‖ ≤ C) →
    ∀ w : ℕ → E,
      OnlineLearningOCO.FoReL.IsFoReLRun K (fun t v => l t v)
        (fun v => R v / (Real.sqrt (μ * B / T) / C)) w →
      (1 / (T : ℝ)) * (∑ t ∈ Finset.Icc 1 T, l t (w t) -
          sInf ((fun v => ∑ t ∈ Finset.Icc 1 T, l t v) '' K)) ≤
        c * C * Real.sqrt B * μ ^ (-(1 / 2 : ℝ)) * (T : ℝ) ^ (-(1 / 2 : ℝ)) := by sorry

end OfflineToOnline
