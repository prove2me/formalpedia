-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_CellNetwork_diagram_compatible
-- name    : OAI.OneWayLiveness.CellNetwork.diagram_compatible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:10:46.145376+00:00
-- url     : https://prove2.me/theorems/95fe3f59-33fe-480c-84d0-14567773273b
-- title:
--   Boundary colorings compatible with a cell diagram are exactly those extending to the cell's tips
-- statement:
--   Let $Q$ be a finite set (of automaton states). A *slot* is a triple $\sigma=(d,p,q)\in\{0,1\}\times Q\times Q$, and a *port* is a pair $(\sigma,\ell)$ of a slot and a lane $\ell\in\{0,1\}$. A cell has two kinds of *incidences*. There is a boundary incidence $(s,\sigma)$ for each side $s\in\{0,1\}$ (left or right) and each slot $\sigma$, and a stay incidence $((p,q),\theta)$ for each $(p,q)\in Q\times Q$ and role $\theta\in\{0,1\}$. Each incidence $j$ has two *tips*, $(j,0)$ and $(j,1)$. Write $\oplus$ for exclusive or of bits.
--
--   Let $\pi$ be a permutation of the incidences. The cell diagram $D_\pi$ is the perfect matching of $\mathrm{Ports}_{\mathrm L}\sqcup\mathrm{Ports}_{\mathrm R}$ obtained from the following wiring by following paths and discarding closed loops:
--   - *lanes* join the port $(\sigma,\ell)$ on side $s$ to the tip $((s,\sigma),\,s\oplus\ell)$;
--   - lanes also join each stay tip $(((p,q),\theta),t)$ to $(((p,q),\neg\theta),\neg t)$;
--   - *joins* connect the tip $(j,0)$ to $(\pi(j),1)$ for every incidence $j$.
--
--   A pair of colorings $l,r:\mathrm{Ports}\to\{0,1\}$ of the left and right ports is *compatible* with $D_\pi$ if any two ports matched by $D_\pi$ receive equal colors.
--
--   **Theorem.** $D_\pi$ is compatible with $(l,r)$ if and only if there is a coloring $g$ of the tips such that, with $c_0=l$ and $c_1=r$,
--   $$
--   \begin{aligned}
--   &c_s(\sigma,\ell)=g\big((s,\sigma),\,s\oplus\ell\big) &&\text{for all sides } s,\ \text{slots } \sigma,\ \text{lanes } \ell,\\
--   &g\big(((p,q),\theta),t\big)=g\big(((p,q),\neg\theta),\neg t\big) &&\text{for all } p,q\in Q,\ \theta,t\in\{0,1\},\\
--   &g(j,0)=g\big(\pi(j),1\big) &&\text{for all incidences } j.
--   \end{aligned}
--   $$
--
--   In words, a boundary coloring is compatible with the contracted cell diagram exactly when it extends to a coloring of all internal tips that is constant along every lane and every join. This replaces a global matching by local equations. It is applied to every cell of an input word at once to characterize the colorings compatible with the full diagram of the word.
--
--   **Formalization Note** The cell diagram is `diagram Q π : Pairing (Port Q ⊕ Port Q)`, and compatibility is `Pairing.Compatible (Sum.elim left right)`. Tips are `Tip Q = Incidence Q × Bool`, and the bit $s\oplus\ell$ is `tipRole s l`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Cells.lean#L117-L137

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.CellNetwork
variable (Q : Type)

theorem OAI.OneWayLiveness.CellNetwork.diagram_compatible [Fintype Q] (r : Equiv.Perm (Incidence Q))
    (left right : Port Q → Bool) :
    (diagram Q r).Compatible (Sum.elim left right) ↔ ∃ f : Tip Q → Bool,
    (∀ s slot l, (if s then right else left) (slot,l) = f (.inl (s,slot),tipRole s l)) ∧
    (∀ pq role t, f (.inr (pq,role),t) = f (.inr (pq,!role),!t)) ∧
    (∀ i, f (i,false) = f (r i,true)) := by sorry
