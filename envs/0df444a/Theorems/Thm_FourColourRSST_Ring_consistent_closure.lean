-- Prove2me | Theorems.Thm_FourColourRSST_Ring_consistent_closure
-- name    : FourColourRSST.Ring.consistent_closure
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:58.491594+00:00
-- url     : https://prove2.me/theorems/014b5eff-5e26-415e-abd9-b1f0b4681cac
-- title:
--   §3, p. 8 — the null set is consistent, unions of consistent sets are consistent, and every set has a unique maximal consistent subset
-- statement:
--   Let $R$ be a circuit of length $k \ge 3$. Then:
--
--   1. the empty set of edge-colourings of $R$ is consistent;
--   2. if $\mathcal C_1$ and $\mathcal C_2$ are consistent, so is $\mathcal C_1 \cup \mathcal C_2$;
--   3. every set $\mathcal S$ of edge-colourings of $R$ has a unique maximal consistent subset $\mathcal S'$, in the sense that there is exactly one $\mathcal S' \subseteq \mathcal S$ which is consistent and contains every consistent subset of $\mathcal S$:
--   $$\exists!\, \mathcal S' \subseteq \mathcal S:\quad \mathcal S' \text{ consistent and } \bigl(\mathcal T \subseteq \mathcal S,\ \mathcal T \text{ consistent} \implies \mathcal T \subseteq \mathcal S'\bigr).$$
--
--   The maximal consistent subset $\mathcal S'$ is the object the reducibility computations of §3 evaluate; the paper notes that for rings of small size it can be computed from $\mathcal S$ by machine.
--
--   **Formalization Note.** "Maximal" is rendered as greatest (contains every consistent subset of $\mathcal S$), which is the meaning the paper's "unique maximal" carries given closure under unions. The circuit is `cycleGraph k` on `Fin k`, with $k \ge 3$ restricting to the circuits this encoding represents.
-- source:
--   Robertson, Sanders, Seymour and Thomas, The Four-Colour Theorem, J. Combin. Theory Ser. B 70 (1997), author's manuscript (rev. 16 January 1997), p. 8, §3, "Since the null set is consistent, and the union of any two consistent sets is consistent, it follows that any set of edge-colourings 𝒮 has a unique maximal consistent subset 𝒮′"

import Mathlib
import Definitions.Def_FourColourRSST_Ring_Setting

namespace FourColourRSST.Ring

theorem consistent_closure {k : ℕ} [NeZero k] (hk : 3 ≤ k) :
    Consistent (∅ : Set (EdgeColouring k)) ∧
    (∀ C₁ C₂ : Set (EdgeColouring k), Consistent C₁ → Consistent C₂ → Consistent (C₁ ∪ C₂)) ∧
    (∀ S : Set (EdgeColouring k), ∃! S' : Set (EdgeColouring k),
      S' ⊆ S ∧ Consistent S' ∧ ∀ T ⊆ S, Consistent T → T ⊆ S') := by sorry

end FourColourRSST.Ring
