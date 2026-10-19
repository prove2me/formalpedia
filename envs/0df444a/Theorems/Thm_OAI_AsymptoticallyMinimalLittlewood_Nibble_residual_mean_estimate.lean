-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_residual_mean_estimate
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_mean_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:17:15.475331+00:00
-- url     : https://prove2.me/theorems/08e38ca8-4e86-4410-b013-82cf3d085400
-- title:
--   Expected residual degree after a random selection of edges in an almost regular hypergraph
-- statement:
--   Let $V$ be a set of vertices and $E$ a finite set of edge labels. A hypergraph is given by a finite set $S\subseteq E$ of edges together with a finite vertex set $A_e\subseteq V$ for every label $e$. For a vertex $v$ let $S(v)=\{e\in S: v\in A_e\}$ be the set of edges containing $v$ and $\deg_S(v)=|S(v)|$ its degree; for vertices $v\ne w$ the number $|S(v)\cap S(w)|$ is their codegree. For a finite vertex set $X$ let $H_S(X)=\bigcup_{x\in X}S(x)=\{f\in S: A_f\cap X\ne\emptyset\}$ be the set of edges of $S$ meeting $X$.
--
--   A random selection of edges is a configuration $s\colon E\to\{0,1\}$ ($s_f=1$ meaning that $f$ is selected), weighted by $w_p(s)=\prod_{f\in E}p^{s_f}(1-p)^{1-s_f}$; for $g\colon\{0,1\}^E\to\mathbb{R}$ write $\mathbb{E}_p[g]=\sum_s w_p(s)\,g(s)$, which for $0\le p\le 1$ is the expectation when every label is selected independently with probability $p$. For $F\subseteq E$ let $N_F(s)=\prod_{f\in F}(1-s_f)$ be the indicator that no edge of $F$ is selected. For a vertex $v$ define the residual-degree statistic
--   $Y_v(s)=\sum_{e\in S(v)}N_{H_S(A_e\setminus\{v\})}(s)$, the number of edges $e\ni v$ of $S$ such that no selected edge of $S$ meets $A_e\setminus\{v\}$.
--
--   Let $U\subseteq V$ be finite and let $r\ge1$ be an integer. Let $D,\varepsilon,C,p,a$ be real numbers with $D>0$, $0\le\varepsilon\le D$, $0\le C\le aD$, $0\le p\le1$, $a\ge0$, $pD=a$ and $ra\le1$. Assume that the hypergraph is $r$-uniform on $U$ ($A_e\subseteq U$ and $|A_e|=r$ for all $e\in S$), almost $D$-regular ($|\deg_S(v)-D|\le\varepsilon$ for all $v\in U$), and has codegrees at most $C$ ($|S(v)\cap S(w)|\le C$ for all distinct $v,w\in U$). Then for every $v\in U$,
--
--   $$
--   \Big|\,\mathbb{E}_p[Y_v]-\big(1-(r-1)a\big)D\Big|\le(1+2ra)\,\varepsilon+6r^2a^2D.
--   $$
--
--   Heuristically, each of the $r-1$ other vertices of an edge at $v$ is hit by a selected edge with probability about $pD=a$, so an edge at $v$ survives with probability about $1-(r-1)a$. The theorem makes this precise: the expected residual degree is $(1-(r-1)a)D$ up to an error that is linear in the irregularity $\varepsilon$ and quadratic in $a$. It is the first-moment input for one round of the nibble method.
--
--   **Formalization Note** $S(v)$, $H_S(X)$ and $N_F$ are `incident S A v`, `hits S A X` and `noHit F`; $\mathbb{E}_p$ is `expectation p`, and configurations are functions `E → Bool`. The factor $r-1$ is the natural-number subtraction `r - 1` cast to the reals; since $r\ge1$ it equals the real number $r-1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Nibble.lean#L472-L529

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Nibble
universe uI uE uV
open scoped BigOperators
open Finset
variable {V : Type uV} {E : Type uE} [DecidableEq V] [Fintype E] [DecidableEq E]

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_mean_estimate (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} (hr0 : 1 ≤ r) {D ε C p a : ℝ}
    (hD : 0 < D) (he : 0 ≤ ε) (heD : ε ≤ D) (hC : 0 ≤ C) (hCa : C ≤ a*D)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) (hpa : p*D = a)
    (hra : (r : ℝ)*a ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card = r)
    (hdeg : ∀ v ∈ U, |((incident S A v).card : ℝ) - D| ≤ ε)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (hv : v ∈ U) :
    |expectation p (fun s ↦ ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s) -
      (1 - ((r-1 : ℕ) : ℝ)*a)*D| ≤ (1+2*(r : ℝ)*a)*ε + 6*(r : ℝ)^2*a^2*D := by sorry
