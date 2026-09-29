-- Prove2me | Theorems.Thm_LocalSearchFL_MultiSwap_capture_disjoint_mono
-- name    : LocalSearchFL.MultiSwap.capture_disjoint_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:38:15.316514+00:00
-- url     : https://prove2.me/theorems/af62440d-97ac-4eb6-9b53-84f66e5ba19c
-- title:
--   §3.4 — capture of disjoint sets is disjoint, and capture is monotone
-- statement:
--   Let $S$ and $O$ be two solutions with client assignments $\sigma_S$ and $\sigma_O$, and let $\mathrm{capture}(A) = \{o \in O \mid |N_S(A) \cap N_O(o)| > |N_O(o)|/2\}$. For all $X, Y \subseteq S$:
--
--   1. if $X \cap Y = \emptyset$, then $\mathrm{capture}(X) \cap \mathrm{capture}(Y) = \emptyset$;
--   2. if $X \subseteq Y$, then $\mathrm{capture}(X) \subseteq \mathrm{capture}(Y)$.
--
--   These two facts let the partition of $S$ and $O$ used in the analysis compute captures against the original solutions throughout.
--
--   **Formalization Note** The paper writes $X \subset Y$; the statement is given for $X \subseteq Y$, which contains it.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 551, §3.4

import Mathlib
import Definitions.Def_LocalSearchFL_MultiSwap_capture

namespace LocalSearchFL.MultiSwap

/-- §3.4, p. 551: for `X, Y ⊆ S`, if `X` and `Y` are disjoint then `capture(X)` and `capture(Y)`
are disjoint, and if `X ⊆ Y` then `capture(X) ⊆ capture(Y)`. -/
theorem capture_disjoint_mono {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O X Y : Finset Fa) (hX : X ⊆ S) (hY : Y ⊆ S) :
    (Disjoint X Y → Disjoint (capture σS σO O X) (capture σS σO O Y)) ∧
      (X ⊆ Y → capture σS σO O X ⊆ capture σS σO O Y) := by sorry

end LocalSearchFL.MultiSwap
