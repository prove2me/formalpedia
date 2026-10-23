-- Prove2me | Theorems.Thm_NeedPersuasion_FirstBest_lemma_2_lex
-- name    : NeedPersuasion.FirstBest.lemma_2_lex
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-22T22:26:50.972555+00:00
-- url     : https://prove2.me/theorems/d79db781-b9c7-4d1c-8be4-5b1c4376a773
-- title:
--   Lemma 2 + footnote 12 — lexicographic optima sm(0), sm(1), ap(0), ap(1) exist
-- statement:
--   Existence of lexicographically optimal signaling mechanisms and admission policies (Lemma 2 with the refinement of footnote 12).
--
--   Consider the two-type queueing model with arrival rates $\lambda_L>0$, $\lambda_H\ge 0$, $\lambda=\lambda_L+\lambda_H\le 1$, utilities $u_L,u_H$ satisfying the standing assumptions and Assumption 1. Let $\Pi_{AP}$ be the class of admission policies (steady-state distributions $\pi$ on $\mathbb N_0$ with $\lambda_H\pi_n\le\pi_{n+1}\le\lambda\pi_n$ and finite welfare) and $\Pi_{SM}\subseteq\Pi_{AP}$ the obedient signaling mechanisms (those also satisfying (JOIN) $J(\pi)\ge0$ and (LEAVE) $L(\pi)\le 0$). Write $W_L(\pi)$ and $W_H(\pi)$ for the welfare of the two types.
--
--   Assume that $\lambda<1$, or that $\lim_{k\to\infty}u_L(k)=\lim_{k\to\infty}u_H(k)=-\infty$, and that $\sum_k\lambda_H^k u_H(k)$ converges. Then for each class $\Pi\in\{\Pi_{SM},\Pi_{AP}\}$ both lexicographic optimization problems have a solution:
--
--   1. there is $\pi\in\Pi$ maximizing $W_H$ over $\Pi$ such that $W_L(\pi)\ge W_L(\pi')$ for every maximizer $\pi'$ of $W_H$ over $\Pi$;
--   2. there is $\pi\in\Pi$ maximizing $W_L$ over $\Pi$ such that $W_H(\pi)\ge W_H(\pi')$ for every maximizer $\pi'$ of $W_L$ over $\Pi$.
--
--   These are the optimizers $\mathrm{sm}(0),\mathrm{sm}(1)$ (for $\Pi_{SM}$) and $\mathrm{ap}(0),\mathrm{ap}(1)$ (for $\Pi_{AP}$) of the weighted welfare $W(\pi,\theta)=\theta W_L(\pi)+(1-\theta)W_H(\pi)$ at the extreme weights, where footnote 12 replaces plain maximization by this lexicographic refinement. Together with Lemma 2 (existence of maximizers of $W(\cdot,\theta)$ for $\theta\in(0,1)$) it shows that the optimal sets $\mathrm{sm}(\theta)$ and $\mathrm{ap}(\theta)$ compared in Theorem 6 are non-empty for every $\theta\in[0,1]$.
--
--   **Formalization Note** `lexArgmax S f h` is the set of $\pi\in S$ that maximize $f$ over $S$ and, among the maximizers of $f$, maximize $h$. The hypotheses are exactly those of the platform statement of Lemma 2. The proof in the paper (compactness of $\Pi_{AP}$, $\Pi_{SM}$ or of the relevant closures via Prohorov's theorem, and continuity of $W_L,W_H$) gives this refinement as well: the set of maximizers of a continuous function on a compact set is compact, so the second criterion also attains its maximum on it.
-- source:
--   arXiv:2005.07253v3, Lemma 2 (Existence), p. 14, and its proof in the appendix (proofs of Section 3, structural characterization); lexicographic refinement at θ ∈ {0,1} from footnote 12, p. 13

import Mathlib
import Definitions.Def_NeedPersuasion_FirstBest_Model
import Definitions.Def_NeedPersuasion_FirstBest_Objects

namespace NeedPersuasion.FirstBest

theorem lemma_2_lex (M : Model) (hM : M.Standing)
    (hExist : M.lam < 1 ∨ (Filter.Tendsto M.uL Filter.atTop Filter.atBot ∧
      Filter.Tendsto M.uH Filter.atTop Filter.atBot))
    (hSumH : Summable (fun k => M.lamH ^ k * M.uH k)) :
    (lexArgmax (PiSM M) (WH M) (WL M)).Nonempty ∧ (lexArgmax (PiSM M) (WL M) (WH M)).Nonempty ∧
    (lexArgmax (PiAP M) (WH M) (WL M)).Nonempty ∧
      (lexArgmax (PiAP M) (WL M) (WH M)).Nonempty := by sorry

end NeedPersuasion.FirstBest
