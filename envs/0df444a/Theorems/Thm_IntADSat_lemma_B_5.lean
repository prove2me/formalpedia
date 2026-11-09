-- Prove2me | Theorems.Thm_IntADSat_lemma_B_5
-- name    : IntADSat.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:51.763677+00:00
-- url     : https://prove2.me/theorems/89b0ac6d-401e-4cab-bc5c-084b3b46bbb8
-- title:
--   Lemma B.5 — degree classes and the low-degree count
-- statement:
--   Let $G\sim G(n,1/2)$ and let $k=\lfloor n^{0.02}\rfloor$, $K=\lceil10\sqrt n\rceil$, $s=\lfloor n^{0.505}\rfloor$, $t=\lfloor (n-1)/2-\sqrt{0.245\,n\log n}\rfloor$ be the parameters of (B.1). With probability $1-o(1)$ all three assertions hold:
--
--   1. every degree class has fewer than $K$ vertices;
--   2. every degree class of degree at most $t$ has fewer than $k$ vertices;
--   3. at least $2s$ vertices have degree at most $t-K$.
--
--   A degree class is the set of vertices sharing one degree. These are the size bounds used to pick the row sets of the two rounds of the integer construction.
--
--   Differences from the source:
--   - reading: all three assertions hold with probability 1 − o(1) → Tendsto of the probability of the event to 1 as n → ∞; reason: the meaning of 1 − o(1)
--   - encoding: every degree class → for every vertex v, the class {u : deg u = deg v}; reason: the classes of degrees that occur
--   - encoding: parameters k, K, s, r, g, t of (B.1) → kP, KP, sP, rP, gP (Nat.floor/Nat.ceil of real powers) and tP (Int.floor, natural log); reason: same values
--   - encoding: G ∼ G(n, 1/2) on the labelled vertex set [n] → erProb n (1/2) on SimpleGraph (Fin n) (published Erdős–Rényi product weight at edge probability 1/2); reason: same law: every labelled graph has probability 2^(−n(n−1)/2)
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.5, pp.16–17 (PDF 17–18)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_IntADSat_deg
import Definitions.Def_IntADSat_kP
import Definitions.Def_IntADSat_KP__d24af9
import Definitions.Def_IntADSat_sP
import Definitions.Def_IntADSat_tP

set_option autoImplicit false

namespace IntADSat

/-- **Lemma B.5** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), pp.16–17 (PDF 17–18)). For `G ∼ G(n, 1/2)`, with probability `1 − o(1)` all
three assertions hold: (1) every degree class has fewer than `K` vertices; (2) every degree class of
degree at most `t` has fewer than `k` vertices; (3) at least `2s` vertices have degree at most `t − K`.
Here `k, K, s, t` are the parameters of display (B.1).

**Formalization Note** "With probability `1 − o(1)`" is convergence of the probability to `1`; a degree
class is the set of vertices sharing the degree of some vertex `v`. -/
theorem lemma_B_5 :
    Filter.Tendsto (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (1 / 2) (fun G =>
        (∀ v, (Finset.univ.filter fun u => deg G u = deg G v).card < KP n) ∧
        (∀ v, (deg G v : ℤ) ≤ tP n → (Finset.univ.filter fun u => deg G u = deg G v).card < kP n) ∧
        2 * sP n ≤ (Finset.univ.filter fun v => (deg G v : ℤ) ≤ tP n - KP n).card))
      Filter.atTop (nhds 1) := by sorry

end IntADSat
