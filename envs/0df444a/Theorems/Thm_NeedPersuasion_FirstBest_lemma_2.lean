-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_lemma_2
-- name    : NeedPersuasion.FirstBest.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:41.706852+00:00
-- url     : https://prove2.me/theorems/63f7feeb-6b38-4758-854f-a0379c85084d
-- title:
--   Lemma 2, p. 14 — maximizers of W(·, θ) exist over Π_SM and over Π_AP
-- statement:
--   Suppose $\lambda<1$, or $\lambda=1$ and $\lim_{k\to\infty}u_i(k)=-\infty$ for both $i\in\{L,H\}$. Then for every $\theta\in[0,1]$ there is a signaling mechanism maximizing $W(\pi,\theta)$ over all $\pi\in\Pi_{SM}$, and an admission policy maximizing $W(\pi,\theta)$ over all $\pi\in\Pi_{AP}$:
--   $$\exists\,\pi^\star\in\Pi_{SM}:\ W(\pi^\star,\theta)=\max_{\pi\in\Pi_{SM}}W(\pi,\theta),\qquad \exists\,\pi^\star\in\Pi_{AP}:\ W(\pi^\star,\theta)=\max_{\pi\in\Pi_{AP}}W(\pi,\theta).$$
--
--   Existence is what makes $\mathrm{sm}(\theta)$ and $\mathrm{ap}(\theta)$ non-empty.
--
--   **Formalization Note** The hypothesis that $\sum_k\lambda_H^ku_H(k)$ converges is added. Under the mission's convention that admission policies have finite welfare, without it $\Pi_{AP}$ is empty when $\lambda_H>0$ and $u_H$ decreases fast enough, and no maximizer exists; with it, every threshold policy has finite welfare. The page's "$\lim_{n\to\infty}u_i(k)$" is read as $\lim_{k\to\infty}u_i(k)$.
-- source:
--   arXiv:2005.07253v3, Lemma 2, p. 14

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

namespace NeedPersuasion.FirstBest

theorem lemma_2 (M : Model) (hM : M.Standing)
    (hExist : M.lam < 1 ∨ (Filter.Tendsto M.uL Filter.atTop Filter.atBot ∧
      Filter.Tendsto M.uH Filter.atTop Filter.atBot))
    (hSumH : Summable (fun k => M.lamH ^ k * M.uH k)) :
    ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (argmaxW M (PiSM M) θ).Nonempty ∧ (argmaxW M (PiAP M) θ).Nonempty := by sorry

end NeedPersuasion.FirstBest
