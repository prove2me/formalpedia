-- Prove2me | Theorems.Thm_LPCommunity_Tight_lemma_1
-- name    : LPCommunity.Tight.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:11.650843+00:00
-- url     : https://prove2.me/theorems/624163b8-4f2a-45e3-8508-906b9eb5f672
-- title:
--   Lemma 1, p. 5 — existence of regular bipartite and regular graphs
-- statement:
--   Let $t$ be a positive even integer.
--
--   1. For every integer $d$ with $0\le d\le t/2$, there is a simple $d$-regular bipartite graph on $t$ vertices, with $t/2$ vertices in each side of its bipartition.
--   2. For every integer $d$ with $0\le d\le t-1$, there is a simple $d$-regular graph on $t$ vertices.
--
--   These two existence results supply the regular within-community and cross-community graph pieces used in the construction of Theorem 2.
--
--   **Formalization Note** The two statements are the conjuncts of one Lean theorem. A finite vertex set is represented by `Fin t`; the bipartition is witnessed by a set $A$ of exactly $t/2$ vertices, and every edge has one endpoint in $A$. The degree condition uses Mathlib's `SimpleGraph.IsRegularOfDegree`.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 5, Lemma 1

import Mathlib
import Definitions.Def_LPCommunity_MinBisect_Setting

namespace LPCommunity.Tight

noncomputable local instance {t : ℕ} (H : SimpleGraph (Fin t)) : H.LocallyFinite :=
  fun _ => Fintype.ofFinite _

/-- Del Pia–Khajavirad–Kunisky, Lemma 1, p. 5. -/
theorem lemma_1 :
    (∀ (t d : ℕ), 0 < t → Even t → d ≤ t / 2 →
      ∃ (H : SimpleGraph (Fin t)) (A : Finset (Fin t)),
        LPCommunity.MinBisect.IsBisection t A ∧
        (∀ u v, H.Adj u v → (u ∈ A ↔ v ∉ A)) ∧
        H.IsRegularOfDegree d) ∧
    (∀ (t d : ℕ), 0 < t → Even t → d ≤ t - 1 →
      ∃ H : SimpleGraph (Fin t), H.IsRegularOfDegree d) := by sorry

end LPCommunity.Tight
