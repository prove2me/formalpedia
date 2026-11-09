-- Prove2me | Theorems.Thm_HybridXorLift_lemma_4_2
-- name    : HybridXorLift.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:23:12.007017+00:00
-- url     : https://prove2.me/theorems/62907582-bb39-45d6-9881-6ad541eb3d0a
-- title:
--   Lemma 4.2 — weighted potential: $\sum_y F_z(hy) \le F_z(h)$ and $\sum_{h\in S}\Delta^{z_{J(h)}}(h) \le F_z(\varnothing) = (1+e^{2-0.48r/q})^n - 1$
-- statement:
--   Throughout, $n \ge 1$, $r \ge 1$, $q \ge 1$ are integers and $A$ is a parallel $q$-query hybrid algorithm on the $nr$ physical bits (the standing assumptions of Sections 3–5).
--
--   For every outer string $z$:
--
--   1. for every internal history $h$,
--   $$
--   \sum_y F_z(hy) \le F_z(h); \tag{4.11}
--   $$
--   2. for every antichain $S$ of histories (no member is a strict ancestor of another),
--   $$
--   \sum_{h \in S} \Delta^{z_{J(h)}}(h) \le F_z(\varnothing) = \Big(1 + \exp\Big[2 - 0.48\,\frac{r}{q}\Big]\Big)^n - 1. \tag{4.12}
--   $$
--
--   The weighted potential never increases along the history tree, pointwise for every outer string.
--
--   **Formalization Note** An antichain is given as a finite set of histories; every antichain of the finite history tree is finite.
--
--   Differences from the source:
--   - encoding: histories as sequences of outcomes, hy the child, v ≺ h the strict ancestors → lists of recorded outcomes (Step), h ++ [encodeStep y] the child, proper prefixes the strict ancestors; reason: the record determines the outcome (decodeStep ∘ encodeStep = some), so histories correspond one to one
--   - encoding: partial assignments ξ ∈ {0,1}^J and ζ ∈ {0,1}^Ī → full strings Fin n → Bool read only on J (resp. outside I); averages over full strings; reason: the quantities depend only on the restriction; the average over ζ replicates each restriction 2^|I| times uniformly
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Lemma 4.2, p.16 (PDF p.18)

import Definitions.Def_HybridXorLift_potentialAt
import Definitions.Def_HybridXorLift_delta
import Definitions.Def_HybridXorLift_encodeStep
import Definitions.Def_HybridXorLift_ParallelHybridAlg_histories
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- Lemma 4.2 (Weighted potential) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.16 (PDF p.18). For every outer string `z` and every
internal history `h`, `Σ_y F_z(hy) ≤ F_z(h)` (4.11). For every antichain `S` of histories,
`Σ_{h∈S} Δ^{z_{J(h)}}(h) ≤ F_z(∅) = (1 + exp[2 − 0.48 r/q])ⁿ − 1` (4.12).

**Formalization Note** The standing assumptions of §§3–5 (p.11 (PDF p.13): "we fix integers n ≥ 1, r ≥ 1, q ≥ 1 and a parallel q-query hybrid algorithm on nr physical bits") are explicit hypotheses. Histories are lists of recorded outcomes (`ParallelHybridAlg.histories`); partial assignments are full functions read only on their index set (`cubeAvg`). An antichain is a finite set of histories none of which is a
strict ancestor (proper prefix) of another; every antichain of the finite history tree is
finite. -/
theorem lemma_4_2 {n r : ℕ} {α : Type} (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℕ) (hq : 1 ≤ q)
    (A : ParallelHybridAlg (Fin n × Fin r) α) (hA : A.SlotsAtMost q) (z : Fin n → Bool) :
    (∀ (h : List (Step (Fin n × Fin r))) (k w : ℕ) (S : ParallelSub (Fin n × Fin r) k w)
      (next : (Fin k → (Fin n × Fin r) × Bool) × Fin w → ParallelHybridAlg (Fin n × Fin r) α),
      A.nodeAt h = some (.round k w S next) →
      ∑ y : (Fin k → (Fin n × Fin r) × Bool) × Fin w, potentialAt A q z (h ++ [encodeStep y]) ≤
        potentialAt A q z h) ∧
    (∀ S : Finset (List (Step (Fin n × Fin r))), S ⊆ A.histories →
      (∀ h ∈ S, ∀ h' ∈ S, h <+: h' → h = h') →
      ∑ h ∈ S, delta A q (revealed A h) z h ≤ potentialAt A q z []) ∧
    potentialAt A q z [] = (1 + Real.exp (2 - 0.48 * (r : ℝ) / (q : ℝ))) ^ n - 1 := by sorry

end HybridXorLift
