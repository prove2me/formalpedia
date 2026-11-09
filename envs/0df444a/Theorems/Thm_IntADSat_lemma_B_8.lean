-- Prove2me | Theorems.Thm_IntADSat_lemma_B_8
-- name    : IntADSat.lemma_B_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:32.257327+00:00
-- url     : https://prove2.me/theorems/f6a643c7-7695-4036-826e-4d043d946b21
-- title:
--   Lemma B.8 — first-round integer-surjective cuts
-- statement:
--   Let $G\sim G(n,1/2)$ and let $k,r$ be the parameters of (B.1). For every fixed nonempty $C\subseteq[n]$ with $|C|\le k$, let $S_C$ be the $r$ highest-degree vertices of $G[[n]\setminus C]$, using vertex labels to break ties. With probability $1-o(1)$,
--
--   $$
--   A[C,S_C]\,\mathbb Z^r=\mathbb Z^C\qquad\text{for every such } C .
--   $$
--
--   Differences from the source:
--   - reading: A[C, S_C]ℤ^r = ℤ^C for every such C with probability 1 − o(1) → Tendsto of the probability of the event to 1 as n → ∞; reason: the meaning of 1 − o(1)
--   - reading: using vertex labels to break ties → a smaller label ranks first (topSet); reason: the page does not say which label wins; the lemma holds for any fixed rule
--   - encoding: parameters k, K, s, r, g, t of (B.1) → kP, KP, sP, rP, gP (Nat.floor/Nat.ceil of real powers) and tP (Int.floor, natural log); reason: same values
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.8, p.18 (PDF 19)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_topSet
import Definitions.Def_IntADSat_CutSurj
import Definitions.Def_IntADSat_kP
import Definitions.Def_IntADSat_rP

set_option autoImplicit false

namespace IntADSat

/-- **Lemma B.8** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.18 (PDF 19)). For every fixed nonempty `C ⊆ [n]` with `|C| ≤ k`, let `S_C` be
the `r` highest-degree vertices of `G[[n] ∖ C]`, using vertex labels to break ties. With probability
`1 − o(1)`, `A[C, S_C]ℤ^r = ℤ^C` for every such `C`.

**Formalization Note** One event for all eligible `C` simultaneously; ties are broken in favour of
the smaller label (`topSet`). -/
theorem lemma_B_8 :
    Filter.Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G =>
        ∀ C : Finset (Fin n), C.Nonempty → C.card ≤ kP n → CutSurj G C (topSet G C (rP n))))
      Filter.atTop (nhds 1) := by sorry

end IntADSat
