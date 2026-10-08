-- Prove2me | Theorems.Thm_FourColourRSST_Ring_birkhoff_ring5
-- name    : FourColourRSST.Ring.birkhoff_ring5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:38:03.576505+00:00
-- url     : https://prove2.me/theorems/73f76857-b29e-41f8-83b6-1fa6348a2de8
-- title:
--   (6.4), p. 25 — every non-empty consistent set of edge-colourings of a 5-ring that meets ℰ includes one of 𝒞₁,…,𝒞₅, 𝒟₁,…,𝒟₅, ℰ
-- statement:
--   Let $R$ be a circuit of length 5 with edges $e_1, \dots, e_5$ in order. For $1 \le i \ne j \le 5$ let $\mathcal A_{ij}$ be the equivalence class of the edge-colouring $\kappa$ with $\kappa(e_i) = 1$, $\kappa(e_j) = -1$ and $\kappa(e_k) = 0$ for $k \ne i, j$. For $1 \le i \le 5$ let
--   $$\mathcal C_i = \mathcal A_{ij} \cup \mathcal A_{ik} \cup \mathcal A_{jk},$$
--   where $e_j, e_k \ne e_i$ are the two edges with a common end with $e_i$; and let
--   $$\mathcal D_i = \mathcal A_{ac} \cup \mathcal A_{ad} \cup \mathcal A_{bc} \cup \mathcal A_{bd},$$
--   where $e_a, e_b, e_c, e_d$ are the edges different from $e_i$, in order. Finally let $\mathcal E = \mathcal A_{12} \cup \mathcal A_{23} \cup \mathcal A_{34} \cup \mathcal A_{45} \cup \mathcal A_{15}$.
--
--   **Theorem (Birkhoff).** Every non-empty consistent set $\mathcal C$ of edge-colourings of $R$ with $\mathcal C \cap \mathcal E \neq \emptyset$ satisfies
--   $$\mathcal C_i \subseteq \mathcal C \text{ for some } i, \quad\text{or}\quad \mathcal D_i \subseteq \mathcal C \text{ for some } i, \quad\text{or}\quad \mathcal E \subseteq \mathcal C.$$
--
--   This is Birkhoff's lemma for rings of length 5. In the RSST quadratic colouring algorithm (6.5) it is what allows a 4-colouring to be carried across a separating 5-circuit in the short-circuit subroutine. It is one ingredient of the proof of the Four-Colour Theorem, not the theorem itself.
--
--   **Formalization Note.** The circuit is `cycleGraph 5` on `Fin 5`; the paper's $e_i$ is edge $i - 1$ (0-based). Thus $\mathcal A_{ij}$ is `A (i-1) (j-1)`, $\mathcal E$ = `A 0 1 ∪ A 1 2 ∪ A 2 3 ∪ A 3 4 ∪ A 0 4`, the paper's $\mathcal C_i$ is `C5 (i-1)` (built from edges $i-2$, $i$ modulo 5, the two neighbours of edge $i-1$), and the paper's $\mathcal D_i$ is `D5 (i-1)` with $(a,b,c,d)$ the four other edges read along the path $R - e_i$ starting next to $e_i$. "Includes" is set inclusion and "meets" is non-empty intersection. The hypothesis that $\mathcal C$ is non-empty is implied by meeting $\mathcal E$; it is kept because the statement says it.
-- source:
--   Robertson, Sanders, Seymour and Thomas, The Four-Colour Theorem, J. Combin. Theory Ser. B 70 (1997), author's manuscript (rev. 16 January 1997), p. 25, (6.4)

import Mathlib
import Definitions.Def_FourColourRSST_Ring_Setting

namespace FourColourRSST.Ring

theorem birkhoff_ring5 (C : Set (EdgeColouring 5)) (hC : Consistent C)
    (hne : C.Nonempty) (hmeet : (C ∩ E5).Nonempty) :
    (∃ i, C5 i ⊆ C) ∨ (∃ i, D5 i ⊆ C) ∨ E5 ⊆ C := by sorry

end FourColourRSST.Ring
