-- Prove2me | Theorems.Thm_FourColourRSST_Ring_consistent_union_eqClass
-- name    : FourColourRSST.Ring.consistent_union_eqClass
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:49.040494+00:00
-- url     : https://prove2.me/theorems/9441c9d5-8f22-4f67-982e-21f312843e8d
-- title:
--   §6, p. 25 — every consistent set of edge-colourings is a union of equivalence classes
-- statement:
--   Let $R$ be a circuit of length $k \ge 3$ and let $\mathcal C$ be a consistent set of edge-colourings of $R$ (in the sense of §3: for every $\kappa \in \mathcal C$ and every $\theta \in \{-1,0,1\}$ there is a signed matching $M$ that $\kappa$ $\theta$-fits, and $\mathcal C$ contains every edge-colouring that $\theta$-fits $M$). Then $\mathcal C$ is a union of equivalence classes: for every $\kappa \in \mathcal C$ and every permutation $\lambda$ of $\{-1,0,1\}$, the edge-colouring $\lambda \circ \kappa$ belongs to $\mathcal C$, i.e.
--   $$\kappa \in \mathcal C \implies [\kappa] \subseteq \mathcal C,$$
--   where $[\kappa]$ is the equivalence class of $\kappa$.
--
--   This is the fact that lets the proofs of (6.3) and (6.4) reason class by class: a consistent set that contains one colouring of $\mathcal A_{ij}$ includes all of $\mathcal A_{ij}$, so "meets $\mathcal E$" becomes "includes one of the five classes of $\mathcal E$".
--
--   **Formalization Note.** The circuit is `cycleGraph k` on `Fin k` with edge $i = \{i, i+1\}$. The hypothesis $k \ge 3$ restricts to the circuits this encoding represents; the paper's statement is about any circuit.
-- source:
--   Robertson, Sanders, Seymour and Thomas, The Four-Colour Theorem, J. Combin. Theory Ser. B 70 (1997), author's manuscript (rev. 16 January 1997), p. 25, §6, "every consistent set is a union of equivalence classes"

import Mathlib
import Definitions.Def_FourColourRSST_Ring_Setting

namespace FourColourRSST.Ring

theorem consistent_union_eqClass {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (C : Set (EdgeColouring k)) (hC : Consistent C) :
    ∀ κ ∈ C, eqClass κ ⊆ C := by sorry

end FourColourRSST.Ring
