-- Prove2me | Theorems.Thm_OAI_Barnette_Network_whiteCharge_cut_integral
-- name    : OAI.Barnette.Network.whiteCharge_cut_integral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:22:14.537883+00:00
-- url     : https://prove2.me/theorems/6997bad1-4f5c-4bc0-8fd6-1931bf1600ad
-- title:
--   Pairing a white-charge flow with a scaled cut gradient counts the white vertices inside
-- statement:
--   Let $N$ be a network with finite vertex set $V$ and finite edge set $E$, each edge $e$ having a tail $t(e)$ and a head $h(e)$ in $V$. For $f:V\to\mathbb{R}$ and $x:E\to\mathbb{R}$ let
--   $$
--   (\nabla_N f)(e)=f(h(e))-f(t(e)),\qquad (\partial_N x)(v)=\sum_{e:\,h(e)=v}x(e)-\sum_{e:\,t(e)=v}x(e).
--   $$
--   Let $B\subseteq V$ be an arbitrary set of black vertices, $W=V\setminus B$ the white vertices, and $\rho\in V$ a root. The *white charge* is
--   $$
--   w_\rho(v)=[v\in W]-|W|\,[v=\rho],
--   $$
--   one unit at every white vertex balanced by a sink of size $|W|$ at the root; $[P]$ is $1$ if $P$ holds and $0$ otherwise.
--
--   Let $A\subseteq V$ with $\rho\notin A$, let $\alpha:E\to\mathbb{R}$ satisfy $\partial_N\alpha=w_\rho$, let $c\in\mathbb{R}$, and let $x=c\,\nabla_N\mathbf 1_A$, where $\mathbf 1_A$ is the indicator function of $A$. Then
--
--   $$
--   \sum_{e\in E}\alpha(e)\,x(e)=c\,|A\cap W|.
--   $$
--
--   The left side is the flux of $\alpha$ through the cut of $A$, weighted by $\pm c$ according to the direction of each cut edge. Applied to a flow $\alpha$ realizing the white charge and to a cycle flow $x=c\,\nabla_N\mathbf 1_A$ of the dual, it shows that the integral of $\alpha$ around the cycle has the sign of $c$ as soon as $A$ contains a white vertex.
--
--   **Formalization Note** The white charge is `whiteCharge black root`, with $|W|$ the cardinality of `Finset.univ.filter fun w => ¬black w` cast to $\mathbb{R}$. No colouring condition on the edges is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Circulation.lean#L208-L224

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

theorem OAI.Barnette.Network.whiteCharge_cut_integral (black : V → Prop) (root : V) (A : Finset V)
    (hr : root ∉ A) (α : E → ℝ) (hα : N.boundary α = whiteCharge black root)
    (c : ℝ) (x : E → ℝ)
    (hx : x = c • N.gradient (fun v => if v ∈ A then 1 else 0)) :
    ∑ e, α e * x e = c * ((A.filter fun v => ¬black v).card : ℝ) := by sorry
