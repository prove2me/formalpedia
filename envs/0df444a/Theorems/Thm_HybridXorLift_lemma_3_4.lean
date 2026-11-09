-- Prove2me | Theorems.Thm_HybridXorLift_lemma_3_4
-- name    : HybridXorLift.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:20:44.560078+00:00
-- url     : https://prove2.me/theorems/746bd359-2df8-4763-9b7f-2c3d9e664a81
-- title:
--   Lemma 3.4 — conditioning: $|\Phi^{\xi b}_I(h) - \Phi^\xi_I(h)| \le \Phi^\xi_{I \cup \{i\}}(h)$
-- statement:
--   Throughout, $n \ge 1$, $r \ge 1$, $q \ge 1$ are integers and $A$ is a parallel $q$-query hybrid algorithm on the $nr$ physical bits (the standing assumptions of Sections 3–5).
--
--   Let $J \subseteq [n]$, $\xi \in \{0,1\}^J$, let $I \subseteq \bar J$ be nonempty, and let $i \notin I \cup J$. For $b \in \{0,1\}$ let $\xi b \in \{0,1\}^{J \cup \{i\}}$ extend $\xi$ by $z_i = b$. Then for every history $h$
--   $$
--   \big|\, \Phi^{\xi b}_I(h) - \Phi^\xi_I(h) \,\big| \le \Phi^\xi_{I \cup \{i\}}(h). \tag{3.13}
--   $$
--
--   When the simulator learns one more outer bit, the averaged potentials change by at most a potential of a larger set.
--
--   Differences from the source:
--   - encoding: histories as sequences of outcomes, hy the child, v ≺ h the strict ancestors → lists of recorded outcomes (Step), h ++ [encodeStep y] the child, proper prefixes the strict ancestors; reason: the record determines the outcome (decodeStep ∘ encodeStep = some), so histories correspond one to one
--   - encoding: partial assignments ξ ∈ {0,1}^J and ζ ∈ {0,1}^Ī → full strings Fin n → Bool read only on J (resp. outside I); averages over full strings; reason: the quantities depend only on the restriction; the average over ζ replicates each restriction 2^|I| times uniformly
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Lemma 3.4, p.13 (PDF p.15)

import Definitions.Def_HybridXorLift_phi
import Definitions.Def_HybridXorLift_ParallelHybridAlg_histories
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- Lemma 3.4 (Conditioning) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.13 (PDF p.15). Let `J ⊆ [n]`, `ξ ∈ {0,1}^J`, let
`I ⊆ J̄` be nonempty and `i ∉ I ∪ J`; for `b ∈ {0,1}` let `ξb` extend `ξ` by `z_i = b`. Then
`|Φ^{ξb}_I(h) − Φ^ξ_I(h)| ≤ Φ^ξ_{I∪{i}}(h)` (3.13).

**Formalization Note** The standing assumptions of §§3–5 (p.11 (PDF p.13): "we fix integers n ≥ 1, r ≥ 1, q ≥ 1 and a parallel q-query hybrid algorithm on nr physical bits") are explicit hypotheses. Histories are lists of recorded outcomes (`ParallelHybridAlg.histories`); partial assignments are full functions read only on their index set (`cubeAvg`). `ξb` is `Function.update ξ i b` on the index set
`insert i J`. The paper states the lemma for a history `h`. -/
theorem lemma_3_4 {n r : ℕ} {α : Type} (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℕ) (hq : 1 ≤ q)
    (A : ParallelHybridAlg (Fin n × Fin r) α) (hA : A.SlotsAtMost q)
    (h : List (Step (Fin n × Fin r))) (hh : h ∈ A.histories)
    (J : Finset (Fin n)) (ξ : Fin n → Bool) (I : Finset (Fin n)) (hIJ : I ⊆ Jᶜ) (hI : I.Nonempty)
    (i : Fin n) (hi : i ∉ I ∪ J) (b : Bool) :
    |phi A q I (insert i J) (Function.update ξ i b) h - phi A q I J ξ h| ≤
      phi A q (insert i I) J ξ h := by sorry

end HybridXorLift
