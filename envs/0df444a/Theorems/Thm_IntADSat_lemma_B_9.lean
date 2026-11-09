-- Prove2me | Theorems.Thm_IntADSat_lemma_B_9
-- name    : IntADSat.lemma_B_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:39.036589+00:00
-- url     : https://prove2.me/theorems/cec542a4-ebea-402e-b78f-53ee2ae1d913
-- title:
--   Lemma B.9 — second-round integer-surjective cuts
-- statement:
--   Let $G\sim G(n,1/2)$ and let $K,s,t$ be the parameters of (B.1). For every fixed nonempty $C\subseteq[n]$ with $|C|\le K$, define
--
--   $$
--   R_C=\{v\notin C:\ \deg_{G[[n]\setminus C]}(v)\le t-K\}.
--   $$
--
--   If $|R_C|\ge s$, let $T_C$ be its first $s$ vertices in label order. Then:
--
--   1. with probability $1-o(1)$, simultaneously for every such $C$ with $|R_C|\ge s$, $A[C,T_C]\mathbb Z^s=\mathbb Z^C$;
--   2. for all large $n$, on assertion 3 of Lemma B.5 (at least $2s$ vertices of degree at most $t-K$), $|R_C|\ge s$ for every eligible $C$;
--   3. every vertex of $R_C$ has full degree at most $t$ (for every $n$, every graph and every $C$ with $|C|\le K$).
--
--   Differences from the source:
--   - reading: A[C, T_C]ℤ^s = ℤ^C simultaneously for every such C with probability 1 − o(1) → Tendsto of the probability of the event to 1 as n → ∞; reason: the meaning of 1 − o(1)
--   - reading: "On assertion 3 of Lemma B.5, |R_C| ≥ s", under (B.1)'s "for sufficiently large n" → eventually in n, for every graph satisfying assertion 3 and every eligible C; reason: deterministic consequence for large n
--   - generalization: every vertex of R_C has full degree at most t (eligible C, large n) → every n, every graph, every C with |C| ≤ K (C may be empty); reason: deterministic; restoring C adds at most |C| ≤ K to a degree; specializes to the source's case
--   - encoding: parameters k, K, s, r, g, t of (B.1) → kP, KP, sP, rP, gP (Nat.floor/Nat.ceil of real powers) and tP (Int.floor, natural log); reason: same values
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.9, p.18 (PDF 19)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_lowSet
import Definitions.Def_IntADSat_firstLabels
import Definitions.Def_IntADSat_CutSurj
import Definitions.Def_IntADSat_deg
import Definitions.Def_IntADSat_sP
import Definitions.Def_IntADSat_KP__d24af9
import Definitions.Def_IntADSat_tP

set_option autoImplicit false

namespace IntADSat

/-- **Lemma B.9** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.18 (PDF 19)). For every fixed nonempty `C ⊆ [n]` with `|C| ≤ K`, define
`R_C = {v ∉ C : deg_{G[[n]∖C]}(v) ≤ t − K}`. If `|R_C| ≥ s`, let `T_C` be its first `s` vertices in
label order. With probability `1 − o(1)`, simultaneously for every such `C` with `|R_C| ≥ s`,
`A[C, T_C]ℤ^s = ℤ^C`. On assertion 3 of Lemma B.5, `|R_C| ≥ s` for every eligible `C`. Every vertex of
`R_C` has full degree at most `t`.

**Formalization Note** The second assertion is stated for all large `n` (the "sufficiently large `n`"
of (B.1)); the third holds for every `n`, every graph and every `C` with `|C| ≤ K`. -/
theorem lemma_B_9 :
    Filter.Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G =>
        ∀ C : Finset (Fin n), C.Nonempty → C.card ≤ KP n → sP n ≤ (lowSet G C).card →
          CutSurj G C (firstLabels (lowSet G C) (sP n))))
      Filter.atTop (nhds 1) ∧
    (∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
      2 * sP n ≤ (Finset.univ.filter fun v => (deg G v : ℤ) ≤ tP n - KP n).card →
      ∀ C : Finset (Fin n), C.Nonempty → C.card ≤ KP n → sP n ≤ (lowSet G C).card) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Finset (Fin n)), C.card ≤ KP n →
      ∀ v ∈ lowSet G C, (deg G v : ℤ) ≤ tP n) := by sorry

end IntADSat
