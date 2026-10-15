-- Prove2me | Theorems.Thm_OAI_BufferedIsing_interactionGraph_coupling
-- name    : OAI.BufferedIsing.interactionGraph_coupling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:21:43.052102+00:00
-- url     : https://prove2.me/theorems/8dad959c-3e3c-4476-9fdb-5a23fca67742
-- title:
--   Removing self-loops and relabelling preserve the two-site effective coupling
-- statement:
--   A *finite pair interaction* $P$ on a finite site set $V$ and a finite bond set $E$ consists of maps $\ell,r:E\to V$ and couplings $J_e\ge0$; unlike a graph, it may contain self-loops ($\ell(e)=r(e)$) as well as parallel bonds. For a field $h\in\mathbb{R}^V$ its Gibbs weight is $w^P_h(\sigma)=\exp\big(\sum_{e\in E}J_e\,\sigma_{\ell(e)}\sigma_{r(e)}+\sum_{v\in V}h_v\sigma_v\big)$ for $\sigma\in\{-1,+1\}^V$. Fix the enumeration $\varphi:V\to\{0,\dots,|V|-1\}$ chosen once and for all and let $G_P$ be the finite graph on $\{0,\dots,|V|-1\}$ whose edges are the non-loop bonds of $P$ (enumerated likewise), the bond $e$ joining $\varphi(\ell(e))$ to $\varphi(r(e))$ with coupling $J_e$; write $w^{G_P}_{h'}$ for its Ising weight with field $h'$. For a weight $W$ and sites $x,y$ let $T^{x,y}[W](s,t)=\sum_\sigma\mathbf 1[\sigma_x=s,\ \sigma_y=t]\,W(\sigma)$ be the two-site table, and let $\mathcal K(w)=\tfrac14\big(\log w(+,+)+\log w(-,-)-\log w(+,-)-\log w(-,+)\big)$ be the effective coupling of a $2\times2$ table $w$.
--
--   **Theorem.** For every field $h\in\mathbb{R}^V$ and all distinct sites $u\neq v$ of $V$,
--   $$
--   \mathcal K\Big(T^{\varphi(u),\varphi(v)}\big[w^{G_P}_{h\circ\varphi^{-1}}\big]\Big)=\mathcal K\Big(T^{u,v}\big[w^P_h\big]\Big).
--   $$
--
--   Discarding self-loops and relabelling sites and bonds by integers thus does not change the effective coupling between two distinct sites. This allows results proved for loopless, integer-labelled finite graphs, such as the bound saying that external fields do not increase effective couplings, to be applied to the interactions produced by contracting vertex sets, where self-loops appear naturally.
--
--   **Formalization Note** $P$ is a `PairInteraction V E`; $G_P$ is `interactionGraph P : FiniteGraph (Fintype.card V) (Fintype.card (NonloopEdge P))`, built with `Fintype.equivFin` for both the sites and the non-loop bonds, and $\varphi$ is `Fintype.equivFin V`. $\mathcal K$ is `tableCoupling` and the two-site table is `pairTable`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Contraction.lean#L270-L286

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.interactionGraph_coupling {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (P : PairInteraction V E) (h : V → ℝ) (u v : V) (huv : u ≠ v) :
    tableCoupling (pairTable
      (weight (interactionGraph P) (fun x => h ((Fintype.equivFin V).symm x)))
      (Fintype.equivFin V u) (Fintype.equivFin V v)) =
      tableCoupling (pairTable (interactionWeight P h) u v) := by sorry
