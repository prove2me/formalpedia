-- Prove2me | Theorems.Thm_LNTopology_Local_theorem_3_1
-- name    : LNTopology.Local.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:56.509315+00:00
-- url     : https://prove2.me/theorems/74d99659-a39f-4b9c-b37e-96827dc73c67
-- title:
--   Theorem 3.1, p. 6 — the chain u → v → w is not cost-minimizing; rerouting through u → w is cheaper
-- statement:
--   Let $c$ be a channel cost function satisfying (MO), (SY), (CI) and (SA). Let $u,v,w$ be three distinct nodes and $\lambda_1,\lambda_2>0$. Consider the structure $\overrightarrow{uv}^{\lambda_1},\overrightarrow{vw}^{\lambda_2}$ — the network whose only channels carry $\lambda_1$ from $u$ to $v$ and $\lambda_2$ from $v$ to $w$ — and let $F$ be the flow it supports. Then:
--
--   1. the structure $\overrightarrow{uv}^{\lambda_1},\overrightarrow{vw}^{\lambda_2}$ is not cost-minimizing for $F$;
--   2. if $\lambda_1\le\lambda_2$, the structure $\overrightarrow{uw}^{\lambda_1},\ {}^{\lambda_1}\overleftrightarrow{vw}^{\lambda_2}$ (net flow $\lambda_1$ from $u$ to $w$, net flow $\lambda_2-\lambda_1$ from $v$ to $w$, no channel between $u$ and $v$) is a Lightning Network supporting $F$ with
--   $$
--   c\big(\overrightarrow{uw}^{\lambda_1},{}^{\lambda_1}\overleftrightarrow{vw}^{\lambda_2}\big)<c\big(\overrightarrow{uv}^{\lambda_1},\overrightarrow{vw}^{\lambda_2}\big);
--   $$
--   3. if $\lambda_1\ge\lambda_2$, the structure ${}^{\lambda_2}\overleftrightarrow{uv}^{\lambda_1},\ \overrightarrow{uw}^{\lambda_2}$ (net flow $\lambda_1-\lambda_2$ from $u$ to $v$, net flow $\lambda_2$ from $u$ to $w$, no channel between $v$ and $w$) is a Lightning Network supporting $F$ with strictly lower cost than $\overrightarrow{uv}^{\lambda_1},\overrightarrow{vw}^{\lambda_2}$.
--
--   This is the basic local improvement of the paper: a node that only relays payments from one neighbour to another can be bypassed at strictly lower cost. Both corollaries of §3.1 rest on it.
--
--   **Formalization Note** The three structures are `triangleLN u v w λ₁ λ₂ 0`, `triangleLN u v w 0 (λ₂ − λ₁) λ₁` and `triangleLN u v w (λ₁ − λ₂) 0 λ₂` on an arbitrary finite node set, with every other entry $0$. "The same flow" is expressed through `Supports … f` for the flow $f$ the original structure supports, which is independent of the sign convention (the paper's Figure 1 writes $f_u=-\lambda_1$, the row-sum display gives $f_u=+\lambda_1$). At $\lambda_1=\lambda_2$ both alternatives apply, as the paper notes. (SA) is used in the corrected form $c(x+y)<c(x)+c(y)$ for all $x,y>0$; the printed range "$x>y\ge0$" is unsatisfiable. Cost-minimizing compares with networks on the same node set.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 6 (PDF 7), Theorem 3.1 and Figure 1; proof pp. 9–10 (PDF 10–11), App. A, (1)–(6)

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Local_TriangleLN

namespace LNTopology.Local

/-- Theorem 3.1 (SSRN 4439190, p. 6; proof pp. 9–10): for distinct nodes `u, v, w` and
`l₁, l₂ > 0`, the structure `u →^{l₁} v, v →^{l₂} w` (no other channel) is not cost-minimizing
for the flow `f` it supports; if `l₁ ≤ l₂` the structure `u →^{l₁} w, l₁ ←→_{vw} l₂` is a
Lightning Network supporting the same flow at strictly lower cost, and if `l₂ ≤ l₁` so is
`l₂ ←→_{uv} l₁, u →^{l₂} w`. -/
theorem theorem_3_1 {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ → ℝ) (hc : IsChannelCost c)
    (u v w : V) (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) (l₁ l₂ : ℝ) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) (f : V → ℝ) (hf : Supports (triangleLN u v w l₁ l₂ 0) f) :
    ¬ IsCostMinimizing c f (triangleLN u v w l₁ l₂ 0) ∧
    (l₁ ≤ l₂ → IsLN (triangleLN u v w 0 (l₂ - l₁) l₁) ∧
      Supports (triangleLN u v w 0 (l₂ - l₁) l₁) f ∧
      cost c (triangleLN u v w 0 (l₂ - l₁) l₁) < cost c (triangleLN u v w l₁ l₂ 0)) ∧
    (l₂ ≤ l₁ → IsLN (triangleLN u v w (l₁ - l₂) 0 l₂) ∧
      Supports (triangleLN u v w (l₁ - l₂) 0 l₂) f ∧
      cost c (triangleLN u v w (l₁ - l₂) 0 l₂) < cost c (triangleLN u v w l₁ l₂ 0)) := by sorry

end LNTopology.Local
