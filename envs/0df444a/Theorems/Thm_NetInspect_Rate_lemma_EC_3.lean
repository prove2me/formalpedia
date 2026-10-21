-- Prove2me | Theorems.Thm_NetInspect_Rate_lemma_EC_3
-- name    : NetInspect.Rate.lemma_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:13.035981+00:00
-- url     : https://prove2.me/theorems/3ec03ce9-adac-449a-8dc3-b82ba129e0b2
-- title:
--   Lemma EC.3, pp. ec2–ec3 (body: Lemma 1, p. 13) — the cyclic strategies σ1(S,b1), σ2(T,b2): uniform marginals b1/n, b2/m and (EC.16)
-- statement:
--   Let $S=\{x_0,\dots,x_{n-1}\}$ be a set of $n$ distinct nodes and $T=\{y_0,\dots,y_{m-1}\}$ a set of $m$ distinct components, with $1\le b_1\le n$ and $1\le b_2\le m$. Let $S^k=\{x_k,\dots,x_{k+b_1-1}\}$ (indices mod $n$) and $T^l=\{y_l,\dots,y_{l+b_2-1}\}$ (indices mod $m$) be the cyclic windows, and let $\sigma^1(S,b_1)$ and $\sigma^2(T,b_2)$ put probability $1/n$ on each $S^k$ and $1/m$ on each $T^l$. Then:
--
--   1. $\sigma^1(S,b_1)\in\Delta(\mathcal A_1)$ and $\sigma^2(T,b_2)\in\Delta(\mathcal A_2)$, and every window has exactly $b_1$ (resp. $b_2$) elements;
--   2. (i) each node of $S$ is inspected, and each component of $T$ targeted, with the same probability:
--   $$
--   \rho_{\sigma^1(S,b_1)}(i)=\frac{b_1}{n}\ (i\in S),\qquad \rho_{\sigma^2(T,b_2)}(e)=\frac{b_2}{m}\ (e\in T);
--   $$
--   3. (ii) each node of $S$ lies in exactly $b_1$ of the windows $S^k$, and each component of $T$ in exactly $b_2$ of the windows $T^l$;
--   4. (iii) for every component $e$,
--   $$
--   F(S,\{e\})\le\frac{1}{b_1}\sum_{k=0}^{n-1}F(S^k,\{e\}).
--   $$
--
--   The cyclic strategies are the building blocks of the bounds on the value of the game in Proposition 1.
--
--   **Formalization Note** Windows are indexed from $0$, so window $k$ is the paper's $S^{k+1}$. The hypotheses $b_1\ge 1$ and $b_2\ge 1$ are added: (EC.10) needs $n\ge 1$ and (EC.16) divides by $b_1$. The cyclic strategy adds the probabilities of windows that coincide (which happens only when $b_1=n$), so it is always a probability vector.
-- source:
--   Dahan, Sela & Amin, Network Inspection for Detecting Strategic Attacks, arXiv:1705.00349v4, pp. ec2–ec3, Lemma EC.3, (EC.8)–(EC.16); p. 13, Lemma 1

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

namespace NetInspect.Rate

open Finset DetectionModel

/-- Lemma EC.3 (pp. ec2–ec3): for a set of nodes `S = {x 0, …, x (n-1)}` with `1 ≤ b1 ≤ n` and a
set of components `T = {y 0, …, y (m-1)}` with `1 ≤ b2 ≤ m`, the cyclic strategies
`σ1(S, b1)`, `σ2(T, b2)` are mixed strategies over windows of size exactly `b1`, `b2`, and
(i) (EC.12)–(EC.13), (ii) (EC.14)–(EC.15), (iii) (EC.16) hold. -/
theorem lemma_EC_3 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {n m b1 b2 : ℕ} (x : Fin n → V) (hx : Function.Injective x)
    (y : Fin m → E) (hy : Function.Injective y)
    (hb1 : 1 ≤ b1) (hb1n : b1 ≤ n) (hb2 : 1 ≤ b2) (hb2m : b2 ≤ m) :
    (BlottoLP.Flow.IsMixed (cycStrat x b1) ∧ BlottoLP.Flow.IsMixed (cycStrat y b2)) ∧
    ((∀ k : Fin n, (window x b1 k).card = b1) ∧ (∀ l : Fin m, (window y b2 l).card = b2)) ∧
    ((∀ j : Fin n, marg (cycStrat x b1) (x j) = (b1 : ℝ) / (n : ℝ)) ∧
      (∀ j : Fin m, marg (cycStrat y b2) (y j) = (b2 : ℝ) / (m : ℝ))) ∧
    ((∀ j : Fin n, (univ.filter fun k : Fin n => x j ∈ window x b1 k).card = b1) ∧
      (∀ j : Fin m, (univ.filter fun l : Fin m => y j ∈ window y b2 l).card = b2)) ∧
    (∀ e : E, (G.F (univ.image x) {e} : ℝ) ≤
      (1 / (b1 : ℝ)) * ∑ k : Fin n, (G.F (window x b1 k) {e} : ℝ)) := by sorry

end NetInspect.Rate
