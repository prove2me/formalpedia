-- Prove2me | Theorems.Thm_HybridXorLift_lemma_4_1
-- name    : HybridXorLift.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:19:34.505426+00:00
-- url     : https://prove2.me/theorems/90c5c40b-bb17-41ac-a54b-89bd4ec61df2
-- title:
--   Lemma 4.1 — growth in one subroutine: $\sum_y \Phi^\xi_I(hy) \le (1 + \tfrac2q \sum_{i \in I}\beta_i(h))\Phi^\xi_I(h)$
-- statement:
--   Throughout, $n \ge 1$, $r \ge 1$, $q \ge 1$ are integers and $A$ is a parallel $q$-query hybrid algorithm on the $nr$ physical bits (the standing assumptions of Sections 3–5).
--
--   Fix an internal history $h$; its subroutine has $k(h) \le q$ slots. For every $J \subseteq [n]$, $\xi \in \{0,1\}^J$ and nonempty $I \subseteq \bar J$,
--   $$
--   \sum_y \Phi^\xi_I(hy) \le \Big(1 + \frac{2}{q} \sum_{i \in I} \beta_i(h)\Big)\, \Phi^\xi_I(h), \tag{4.3}
--   $$
--   where $y$ ranges over the complete-basis outcomes of the subroutine at $h$ and $\beta_i(h)$ is the query weight of block $i$.
--
--   This is where the factor $r$ of the main theorem comes from: a subroutine can increase the potentials only in proportion to the query weight it places on the blocks.
--
--   Differences from the source:
--   - encoding: histories as sequences of outcomes, hy the child, v ≺ h the strict ancestors → lists of recorded outcomes (Step), h ++ [encodeStep y] the child, proper prefixes the strict ancestors; reason: the record determines the outcome (decodeStep ∘ encodeStep = some), so histories correspond one to one
--   - encoding: partial assignments ξ ∈ {0,1}^J and ζ ∈ {0,1}^Ī → full strings Fin n → Bool read only on J (resp. outside I); averages over full strings; reason: the quantities depend only on the restriction; the average over ζ replicates each restriction 2^|I| times uniformly
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Lemma 4.1, p.14 (PDF p.16)

import Definitions.Def_HybridXorLift_phi
import Definitions.Def_HybridXorLift_queryWeightAt
import Definitions.Def_HybridXorLift_encodeStep
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- Lemma 4.1 (Growth in one subroutine) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.14 (PDF p.16). Fix an internal history `h`
whose subroutine has `k(h) ≤ q` slots. For every `J ⊆ [n]`, `ξ ∈ {0,1}^J` and nonempty `I ⊆ J̄`,
`Σ_y Φ^ξ_I(hy) ≤ (1 + (2/q) Σ_{i∈I} β_i(h)) Φ^ξ_I(h)` (4.3), the sum running over the outcomes
`y` of the subroutine at `h`.

**Formalization Note** The standing assumptions of §§3–5 (p.11 (PDF p.13): "we fix integers n ≥ 1, r ≥ 1, q ≥ 1 and a parallel q-query hybrid algorithm on nr physical bits") are explicit hypotheses. Histories are lists of recorded outcomes (`ParallelHybridAlg.histories`); partial assignments are full functions read only on their index set (`cubeAvg`). `h` is internal when it reaches a `round` node, whose
outcomes `y` give the children `h ++ [encodeStep y]`; `k(h) ≤ q` follows from `SlotsAtMost q`. -/
theorem lemma_4_1 {n r : ℕ} {α : Type} (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℕ) (hq : 1 ≤ q)
    (A : ParallelHybridAlg (Fin n × Fin r) α) (hA : A.SlotsAtMost q)
    (h : List (Step (Fin n × Fin r))) (k w : ℕ) (S : ParallelSub (Fin n × Fin r) k w)
    (next : (Fin k → (Fin n × Fin r) × Bool) × Fin w → ParallelHybridAlg (Fin n × Fin r) α)
    (hh : A.nodeAt h = some (.round k w S next))
    (J : Finset (Fin n)) (ξ : Fin n → Bool) (I : Finset (Fin n)) (hIJ : I ⊆ Jᶜ) (hI : I.Nonempty) :
    ∑ y : (Fin k → (Fin n × Fin r) × Bool) × Fin w, phi A q I J ξ (h ++ [encodeStep y]) ≤
      (1 + (2 / (q : ℝ)) * ∑ i ∈ I, queryWeightAt A h i) * phi A q I J ξ h := by sorry

end HybridXorLift
