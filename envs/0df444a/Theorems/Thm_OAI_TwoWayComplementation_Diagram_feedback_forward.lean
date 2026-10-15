-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_feedback_forward
-- name    : OAI.TwoWayComplementation.Diagram.feedback_forward
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:30:06.770162+00:00
-- url     : https://prove2.me/theorems/b834a30e-cdf5-45e7-88aa-4986de7c97cf
-- title:
--   Closed form of the left-to-right feedback traversals of a boundary diagram
-- statement:
--   Let $m\in\mathbb{N}$, $[m]=\{0,\dots,m-1\}$, and let $e=(e_{\mathrm f},e_{\mathrm b},e_{\mathrm l},e_{\mathrm r})$ be a boundary diagram on $[m]$: four relations on $[m]$ describing the traversals of a block that enter on the left and leave on the right (forward), enter on the right and leave on the left (backward), and enter and leave on the left, respectively on the right. Relations compose in path order, $(x,z)\in RS\iff\exists y:\ (x,y)\in R\ \text{and}\ (y,z)\in S$, and $R^*$ is the reflexive–transitive closure. Ports are pairs $(s,x)$ of a side $s\in\{\mathrm L,\mathrm R\}$ and a point $x\in[m]$.
--
--   - The port relation $\Pi_e$ joins $(\mathrm L,x)$ to $(\mathrm L,y)$ if $(x,y)\in e_{\mathrm l}$, $(\mathrm L,x)$ to $(\mathrm R,y)$ if $(x,y)\in e_{\mathrm f}$, $(\mathrm R,x)$ to $(\mathrm L,y)$ if $(x,y)\in e_{\mathrm b}$, and $(\mathrm R,x)$ to $(\mathrm R,y)$ if $(x,y)\in e_{\mathrm r}$.
--   - For relations $R$ and $L$ on $[m]$, the bounce relation $\beta$ joins $(\mathrm L,x)$ to $(\mathrm L,y)$ if $(x,y)\in R$, and $(\mathrm R,x)$ to $(\mathrm R,y)$ if $(x,y)\in L$; it never changes the side.
--   - The feedback relation is $\Phi_e(R,L)=\Pi_e\,(\beta\,\Pi_e)^*$.
--
--   Then for all $p,q\in[m]$,
--   $$\big((\mathrm L,p),(\mathrm R,q)\big)\in\Phi_e(R,L)\iff (p,q)\in(e_{\mathrm l}R)^*\;e_{\mathrm f}\;\Big(L\,\big(e_{\mathrm r}\cup e_{\mathrm b}\,R\,(e_{\mathrm l}R)^*\,e_{\mathrm f}\big)\Big)^* .$$
--
--   Here $R$ plays the role of the returns through a context to the left of $e$, which bring the head from the left boundary of $e$ back to it, and $L$ that of the returns through a context on the right. The formula reads: before its first crossing, the traversal may return to the left boundary several times ($e_{\mathrm l}$ followed by a bounce $R$); it then crosses forward ($e_{\mathrm f}$); afterwards, each bounce $L$ on the right is followed either by a right return $e_{\mathrm r}$, or by a backward crossing, a bounce $R$, further left returns and a new forward crossing. This closed form is used to express the surviving through relation of a product $u\,e\,v$ of diagrams by the feedback relation of the middle factor, with $R=u_{\mathrm r}$ and $L=v_{\mathrm l}$.
--
--   **Formalization Note** Sides are `Bool`, with `false` for $\mathrm L$ and `true` for $\mathrm R$; $\Pi_e$, $\beta$ and $\Phi_e(R,L)$ are `e.portRelation`, `bounceRelation R L` and `e.feedback R L`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Diagram.lean#L142-L201

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.feedback_forward {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m))
    {p q : Fin m} :
    ((false, p), (true, q)) ∈ e.feedback R L ↔
      (p, q) ∈ relStar (e.left ○ R) ○ e.forward ○
        relStar (L ○ (e.right ∪ (e.backward ○ R ○ relStar (e.left ○ R) ○ e.forward))) := by sorry
