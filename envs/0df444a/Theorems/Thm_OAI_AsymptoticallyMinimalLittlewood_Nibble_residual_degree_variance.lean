-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Nibble_residual_degree_variance
-- name    : OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_degree_variance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:15:30.544871+00:00
-- url     : https://prove2.me/theorems/c068c430-86e0-4a84-b8dc-34ed4f09cc63
-- title:
--   Variance of the residual degree under a random selection of edges
-- statement:
--   Let $V$ be a set of vertices and $E$ a finite set of edge labels. A hypergraph is given by a finite set $S\subseteq E$ of edges together with a finite vertex set $A_e\subseteq V$ for every label $e$. For a vertex $v$ let $S(v)=\{e\in S: v\in A_e\}$ be the set of edges containing $v$ and $\deg_S(v)=|S(v)|$ its degree; for vertices $v\ne w$ the number $|S(v)\cap S(w)|$ is their codegree. For a finite vertex set $X$ let $H_S(X)=\bigcup_{x\in X}S(x)=\{f\in S: A_f\cap X\ne\emptyset\}$ be the set of edges of $S$ meeting $X$.
--
--   A random selection of edges is a configuration $s\colon E\to\{0,1\}$ ($s_f=1$ meaning that $f$ is selected), weighted by $w_p(s)=\prod_{f\in E}p^{s_f}(1-p)^{1-s_f}$; for $g\colon\{0,1\}^E\to\mathbb{R}$ write $\mathbb{E}_p[g]=\sum_s w_p(s)\,g(s)$, which for $0\le p\le 1$ is the expectation when every label is selected independently with probability $p$. For $F\subseteq E$ let $N_F(s)=\prod_{f\in F}(1-s_f)$ be the indicator that no edge of $F$ is selected. For a vertex $v$ define the residual-degree statistic
--   $Y_v(s)=\sum_{e\in S(v)}N_{H_S(A_e\setminus\{v\})}(s)$, the number of edges $e\ni v$ of $S$ such that no selected edge of $S$ meets $A_e\setminus\{v\}$.
--
--   Let $U\subseteq V$ be finite, let $r\in\mathbb{N}$, and let $D\ge0$, $C\ge0$ and $0\le p\le1$ be real numbers. Assume
--
--   - every edge lies in $U$ and has at most $r$ vertices: $A_e\subseteq U$ and $|A_e|\le r$ for all $e\in S$;
--   - $\deg_S(v)\le D$ for every $v\in U$;
--   - $|S(v)\cap S(w)|\le C$ for all distinct $v,w\in U$.
--
--   Then for every $v\in U$,
--
--   $$
--   \mathbb{E}_p\big[(Y_v-\mathbb{E}_p[Y_v])^2\big]\le p\,r^2D^2C.
--   $$
--
--   If $v$ itself lies in no selected edge, $Y_v(s)$ is exactly the degree of $v$ in the hypergraph that remains after deleting every vertex covered by a selected edge. The theorem bounds the variance of this residual degree by $p\,r^2D^2C$, which is small compared with the square of the mean when codegrees are small; this is the concentration input for one round of the nibble method.
--
--   **Formalization Note** $S(v)$, $H_S(X)$ and $N_F$ are `incident S A v`, `hits S A X` and `noHit F`; $\mathbb{E}_p$ is `expectation p`, and configurations are functions `E → Bool`. The statistic $Y_v$ is introduced by a `let`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Nibble.lean#L98-L135

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

theorem OAI.AsymptoticallyMinimalLittlewood.Nibble.residual_degree_variance (U : Finset V) (S : Finset E) (A : E → Finset V)
    {r : ℕ} {D C p : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hsub : ∀ e ∈ S, A e ⊆ U) (hr : ∀ e ∈ S, (A e).card ≤ r)
    (hdeg : ∀ v ∈ U, ((incident S A v).card : ℝ) ≤ D)
    (hcodeg : ∀ v ∈ U, ∀ w ∈ U, v ≠ w →
      ((incident S A v ∩ incident S A w).card : ℝ) ≤ C)
    (v : V) (hv : v ∈ U) :
    let Y : (E → Bool) → ℝ := fun s ↦
      ∑ e ∈ incident S A v, noHit (hits S A ((A e).erase v)) s
    expectation p (fun s ↦ (Y s - expectation p Y)^2) ≤ p * (r : ℝ)^2 * D^2 * C := by sorry
