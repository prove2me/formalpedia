-- Prove2me | Theorems.Thm_HybridXorLift_lemma_3_3
-- name    : HybridXorLift.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:20:38.804118+00:00
-- url     : https://prove2.me/theorems/37b8c369-a2c3-4c3d-ad20-c6903f8e7bf0
-- title:
--   Lemma 3.3 — likelihood envelope $|\ell_h(z) - \ell^\xi_h| \le \Delta^\xi(h)$
-- statement:
--   Throughout, $n \ge 1$, $r \ge 1$, $q \ge 1$ are integers and $A$ is a parallel $q$-query hybrid algorithm on the $nr$ physical bits (the standing assumptions of Sections 3–5).
--
--   For every history $h$, every $J \subseteq [n]$, every $\xi \in \{0,1\}^J$ and every outer string $z$ with $z_J = \xi$,
--   $$
--   \big|\, \ell_h(z) - \ell^\xi_h \,\big| \le \Delta^\xi(h). \tag{3.12}
--   $$
--
--   Small potentials therefore make the likelihood of a history almost independent of the unknown outer bits.
--
--   Differences from the source:
--   - encoding: histories as sequences of outcomes, hy the child, v ≺ h the strict ancestors → lists of recorded outcomes (Step), h ++ [encodeStep y] the child, proper prefixes the strict ancestors; reason: the record determines the outcome (decodeStep ∘ encodeStep = some), so histories correspond one to one
--   - encoding: partial assignments ξ ∈ {0,1}^J and ζ ∈ {0,1}^Ī → full strings Fin n → Bool read only on J (resp. outside I); averages over full strings; reason: the quantities depend only on the restriction; the average over ζ replicates each restriction 2^|I| times uniformly
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Lemma 3.3, p.13 (PDF p.15)

import Definitions.Def_HybridXorLift_delta
import Definitions.Def_HybridXorLift_avgLikelihood
import Definitions.Def_HybridXorLift_ParallelHybridAlg_histories
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- Lemma 3.3 (Likelihood envelope) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.13 (PDF p.15). For every history `h`, every
`J ⊆ [n]`, every `ξ ∈ {0,1}^J` and every outer string `z` with `z_J = ξ`,
`|ℓ_h(z) − ℓ^ξ_h| ≤ Δ^ξ(h)` (3.12).

**Formalization Note** The standing assumptions of §§3–5 (p.11 (PDF p.13): "we fix integers n ≥ 1, r ≥ 1, q ≥ 1 and a parallel q-query hybrid algorithm on nr physical bits") are explicit hypotheses. Histories are lists of recorded outcomes (`ParallelHybridAlg.histories`); partial assignments are full functions read only on their index set (`cubeAvg`). -/
theorem lemma_3_3 {n r : ℕ} {α : Type} (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℕ) (hq : 1 ≤ q)
    (A : ParallelHybridAlg (Fin n × Fin r) α) (hA : A.SlotsAtMost q)
    (h : List (Step (Fin n × Fin r))) (hh : h ∈ A.histories)
    (J : Finset (Fin n)) (ξ z : Fin n → Bool) (hz : ∀ i ∈ J, z i = ξ i) :
    |likelihood A h z - avgLikelihood A h J ξ| ≤ delta A q J ξ h := by sorry

end HybridXorLift
