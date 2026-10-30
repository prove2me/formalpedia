-- Prove2me | Theorems.Thm_MITMSynthesis_buildS_length_le
-- name    : MITMSynthesis.buildS_length_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:08:33.680872+00:00
-- url     : https://prove2.me/theorems/a9082955-7b92-4106-a392-6febe9b5d9b2
-- title:
--   Size bound $|S_i| \le |V_{n,\mathcal G}|^i$
-- statement:
--   Let $\mathcal G$ be a set of gates, $n \in \mathbb N$, and let `vs` be a duplicate-free list of (layer, unitary) pairs enumerating $V_{n,\mathcal G}$. For every $i \in \mathbb N$,
--
--   $$
--   |S_i| \le |V_{n,\mathcal G}|^i ,
--   $$
--
--   both for the set $S_i$ of unitaries implementable in depth $i$ and for the list $S_i$ that MITM-factor builds from `vs` (starting from $S_0 = [(I, [\,])]$ and multiplying by every element of `vs`).
--
--   This bound is what converts the per-iteration cost of the algorithm into a bound in terms of $|V_{n,\mathcal G}|$.
--
--   Differences from the source:
--   - generalization: |S_i| ≤ |V_{n,G}|^i for the set S_i → the bound for the set S_i and for the list buildS vs i that the algorithm builds; reason: the second conjunct is the source's claim for the set; the first is the same bound for the list representation used by MITM-factor
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §3, p. 6 ("As |S_i| ≤ |V_{n,G}|^i")

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S
import Definitions.Def_MITMSynthesis_mitmFactor

namespace MITMSynthesis

/-- **Size of `S_i`.** Amy–Maslov–Mosca–Roetteler, arXiv:1206.0758v3, §3, p. 6: "|S_i| ≤ |V_{n,G}|^i".
If `vs` enumerates `V_{n,G}` duplicate-free, then for every `i` both the set `S_i` of unitaries
implementable in depth `i` and the list `S_i` built by MITM-factor (`buildS vs i`) have at most
`|V_{n,G}|^i` elements. -/
theorem buildS_length_le {n : ℕ} {G : Set Gate}
    (vs : List (List (Placement n) × Matrix (Q n) (Q n) ℂ)) (hvs : IsLayerEnumeration G vs)
    (i : ℕ) :
    (buildS vs i).val.length ≤ (depthOneSet n G).ncard ^ i ∧
      (S (depthOneSet n G) i).ncard ≤ (depthOneSet n G).ncard ^ i := by sorry

end MITMSynthesis
