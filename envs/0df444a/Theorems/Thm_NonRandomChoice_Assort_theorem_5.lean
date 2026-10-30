-- Prove2me | Theorems.Thm_NonRandomChoice_Assort_theorem_5
-- name    : NonRandomChoice.Assort.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:40.067442+00:00
-- url     : https://prove2.me/theorems/177bdacc-9599-4dc1-8659-182b49a10719
-- title:
--   Theorem 5, p. 14 — with one deterministic product utility, a revenue-ordered assortment is optimal for (13)
-- statement:
--   Let $\mathcal N=\{1,\dots,N\}$ be the products, $0$ the no-purchase option, $\mu>0$ the Gumbel scale, $u_i$ ($i\in\mathcal N$) and $u_0$ the mean utilities, and $i'\in\mathcal N$ the product whose utility is deterministic. With $a_i=\exp(u_i/\mu)$, $a_0=\exp(u_0/\mu)$, $\Lambda=\exp(-u_{i'}/\mu-\gamma)$ ($\gamma$ the Euler–Mascheroni constant) and $\Psi(S^+/\{i'\})=a_0+\sum_{j\in S\setminus\{i'\}}a_j$, the expected revenue of an offer set $S$ is (12):
--   $$R(S)=\begin{cases}\dfrac{\sum_{i\in S}p_i a_i}{a_0+\sum_{j\in S}a_j}, & i'\notin S,\\[2ex] \dfrac{\sum_{i\in S\setminus\{i'\}}p_i a_i}{\Psi(S^+/\{i'\})}\bigl[1-\exp(-\Lambda\Psi(S^+/\{i'\}))\bigr]+p_{i'}\exp(-\Lambda\Psi(S^+/\{i'\})), & i'\in S.\end{cases}$$
--   Suppose the products, $i'$ included, are labelled so that $p_1\ge p_2\ge\dots\ge p_N\ge0$, and let $S_n=\{1,\dots,n\}$ be the revenue-ordered assortments. Then a revenue-ordered assortment is optimal for the assortment problem (13): there is $n\in\{1,\dots,N\}$ such that
--   $$R(S)\le R(S_n)\qquad\text{for every }S\subseteq\mathcal N .$$
--
--   This extends the classical optimality of revenue-ordered assortments under the MNL model (Talluri and van Ryzin 2004) to a choice model that is not MNL once $i'$ is offered, and it makes problem (13) solvable by comparing $N$ candidate sets.
--
--   **Formalization Note** Products are `Fin N` (label $k$ is index $k-1$), $p_1\ge\dots\ge p_N$ is `Antitone p`, and $S_n$ is `roSet N n`. The scale condition $\mu>0$ is implicit on p. 5. The hypothesis $p_i\ge0$ is added: with all prices negative, $\emptyset$ (revenue $0$) is the unique optimum and no $S_n$ with $n\ge1$ is optimal, so the page's claim for $n=1,\dots,N$ needs nonnegative prices. Optimality is over all subsets $S\subseteq\mathcal N$, with $R$ the two-branch revenue (12), not the MNL revenue.
-- source:
--   Wang, What Is the Impact of Non-Randomness on Random Choice Models?, SSRN 3579781 (PDF sha256 93af6c3d…), p. 14, Theorem 5 (with (12)–(13), p. 13)

import Mathlib
import Definitions.Def_NonRandomChoice_Assort_Model

namespace NonRandomChoice.Assort

theorem theorem_5 {N : ℕ} (μ u0 : ℝ) (hμ : 0 < μ) (u : Fin N → ℝ) (ip : Fin N)
    (p : Fin N → ℝ) (hp : Antitone p) (hp0 : ∀ i, 0 ≤ p i) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ ∀ S : Finset (Fin N),
      revenue12 μ u0 u ip p S ≤ revenue12 μ u0 u ip p (roSet N n) := by sorry

end NonRandomChoice.Assort
