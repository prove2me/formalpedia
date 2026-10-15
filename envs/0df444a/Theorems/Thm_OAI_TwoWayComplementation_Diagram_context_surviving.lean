-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_context_surviving
-- name    : OAI.TwoWayComplementation.Diagram.context_surviving
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:30:28.020498+00:00
-- url     : https://prove2.me/theorems/314d6feb-f4e0-4e4e-aa22-e90c1436520c
-- title:
--   The surviving relation of a product $uev$ factors through feedback paths of the middle factor
-- statement:
--   Fix $m\in\mathbb N$ and write $[m]=\{0,1,\dots,m-1\}$ for the set of labels. A *boundary diagram* $a$ on $[m]$ consists of four binary relations on $[m]$: the forward relation $F_a$ (enter on the left side, exit on the right side), the backward relation $B_a$ (enter on the right, exit on the left), the left return relation $L_a$ (enter and exit on the left) and the right return relation $R_a$ (enter and exit on the right). Relations are composed in path order, $XY=\{(x,z):\exists y\ (x,y)\in X,\ (y,z)\in Y\}$, and $X^*$ is the reflexive–transitive closure of $X$. The product $ab$ glues the right side of $a$ to the left side of $b$:
--   $$
--   \begin{aligned}
--   F_{ab}&=F_a\,(L_bR_a)^*\,F_b, & B_{ab}&=B_b\,(R_aL_b)^*\,B_a,\\
--   L_{ab}&=L_a\cup F_a\,(L_bR_a)^*\,L_b\,B_a, & R_{ab}&=R_b\cup B_b\,R_a\,(L_bR_a)^*\,F_b .
--   \end{aligned}
--   $$
--   This product is associative, and the diagrams on $[m]$ form a finite monoid whose identity is $(\Delta,\Delta,\varnothing,\varnothing)$, with $\Delta$ the equality relation.
--
--   For a sign $s\in\{+,-\}$ let $T^+_a=F_a$, $T^-_a=B_a$ (through relations) and $K^+_a=(L_aR_a)^*$, $K^-_a=(R_aL_a)^*$ (loop closures). For diagrams $d,z$ the *surviving relation* of $z$ relative to $d$ is $U^s_d(z)=K^s_d\,T^s_z\,K^s_d$.
--
--   Paths inside a middle factor $e$ are described with *ports* $(\sigma,x)$, where $\sigma\in\{\mathrm{left},\mathrm{right}\}$ is a side and $x\in[m]$ a label.
--   - The port relation $\Pi_e$ joins $(\sigma,x)$ to $(\tau,y)$ when $(x,y)$ lies in $L_e$, $F_e$, $B_e$ or $R_e$, according as $(\sigma,\tau)$ is (left, left), (left, right), (right, left) or (right, right). One step of $\Pi_e$ is one traversal of $e$ from an entry port to an exit port.
--   - For relations $R,L$ on $[m]$, the bounce relation $\beta_{R,L}$ joins $(\mathrm{left},x)$ to $(\mathrm{left},y)$ when $(x,y)\in R$, and $(\mathrm{right},x)$ to $(\mathrm{right},y)$ when $(x,y)\in L$; it never changes the side.
--   - The feedback relation is $\Phi_e(R,L)=\Pi_e\,(\beta_{R,L}\,\Pi_e)^*$: one traversal of $e$, followed by finitely many rounds of a bounce off the surrounding context and another traversal of $e$.
--
--   Let $\mathrm{in}(+)=\mathrm{left}$, $\mathrm{out}(+)=\mathrm{right}$, $\mathrm{in}(-)=\mathrm{right}$, $\mathrm{out}(-)=\mathrm{left}$, and put $G^+=F_u$, $G^-=B_v$, $H^+=F_v$, $H^-=B_u$. For diagrams $d,u,v$ the entry relation (from labels to ports) and the exit relation (from ports to labels) are
--   $$
--   \begin{aligned}
--   (x,(\sigma,y))\in\mathrm{Ent}^s_{d,u,v}&\iff \sigma=\mathrm{in}(s)\ \text{and}\ (x,y)\in K^s_d\,G^s,\\
--   ((\sigma,y),x)\in\mathrm{Ex}^s_{d,u,v}&\iff \sigma=\mathrm{out}(s)\ \text{and}\ (y,x)\in H^s\,K^s_d .
--   \end{aligned}
--   $$
--
--   **Theorem.** For all boundary diagrams $d,u,e,v$ on $[m]$ and both signs $s$,
--   $$
--   U^s_d\big((ue)v\big)=\mathrm{Ent}^s_{d,u,v}\;\Phi_e(R_u,L_v)\;\mathrm{Ex}^s_{d,u,v}.
--   $$
--
--   For $s=+$ this says that $(x,y)\in U^+_d(uev)$, where $uev=(ue)v$, iff one can go from $x$ by a $K^+_d$-path and a forward traversal of $u$ to a label $a$, enter $e$ at the port $(\mathrm{left},a)$, move through $e$ while bouncing back off $u$ (via $R_u$) and off $v$ (via $L_v$) finitely many times until leaving $e$ at a port $(\mathrm{right},b)$, and then reach $y$ by a forward traversal of $v$ and a $K^+_d$-path. The case $s=-$ is the mirror image.
--
--   In the complementation lower bound the labels are states of a two-way automaton (plus one extra label), and the diagram of an input block records which boundary crossings of the block can be joined by a computation inside it. The formula isolates the whole dependence of the surviving relation of $uev$ on the middle factor in the single relation $\Phi_e(R_u,L_v)$. This is what allows one to compare which recurrent classes are lost when the middle factor $e$ is replaced by another diagram $z$ inside a fixed context $u\,\cdot\,v$.
--
--   **Formalization Note** Signs and sides are Booleans: `true` is the positive sign and the right side. The relations $\Pi_e$, $\beta_{R,L}$, $\Phi_e(R,L)$, $\mathrm{Ent}$ and $\mathrm{Ex}$ are `portRelation`, `bounceRelation R L`, `feedback`, `contextEntry` and `contextExit`; the product is `comp`, and the statement is written for `comp (comp u e) v`. No idempotence or other hypothesis on $d,u,e,v$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Diagram.lean#L304-L318

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.context_surviving {m : ℕ} (d u e v : Diagram m) (positive : Bool) :
    d.surviving (comp (comp u e) v) positive =
      contextEntry d u v positive ○ e.feedback u.right v.left ○ contextExit d u v positive := by sorry
