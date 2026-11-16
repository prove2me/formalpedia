-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_quantitative_simultaneous_bound
-- name    : FourWayStream.ARHM.Supplement.quantitative_simultaneous_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:13:05.702195+00:00
-- url     : https://prove2.me/theorems/749f1fbb-82c1-496f-95ac-4e3596b1a88a
-- title:
--   Theorem B.4 — quantitative simultaneous bound $q\ge s[p-\mathbb P[\tau_{\mathrm{for}}<s]]-h_2(p)$
-- statement:
--   Let $N\ge2$ be even, $m\ge1$, $X$ uniform on $\{0,1\}^N$, and $M_1,\dots,M_m$ independent draws from a balanced distribution, independent of $X$ and of the encoding randomness; public coins are allowed. Alice sends any $q$-qubit encoding, and Bob receives all matchings and decodes jointly. Let $p=\mathbb P[G=1]$ be the probability that all answers are correct, over $X$, the matchings and all coins. Then for every integer $s\ge1$,
--   $$q\ \ge\ s\Big[p-\mathbb P\big[\tau_{\mathrm{for}}(M_1,\dots,M_m)<s\big]\Big]-h_2(p).$$
--
--   The bound uses the actual probability of a small transversal forest, so any tail bound, such as $T_{N,m}(s-1)$ from Proposition B.3, can be substituted; no independence between success and the matching list is assumed. It holds for every $s\ge1$, every $m$ and every $p$, without the range restrictions of Theorem 6.7.
--
--   Differences from the source:
--   - encoding: a message of q qubits (classical information included) → a density matrix on C^d with d ≤ 2^q; reason: §4.3 defines q qubits as dimension at most 2^q; same protocols
--   - encoding: a distribution D on perfect matchings of [N] → a distribution on a finite request type Q, request q naming the perfect matching μ(q); reason: Lean convention; with Q the perfect matchings and μ = id it is the source distribution
--   - generalization: Remark 6.2: outputs are legal, e_t ∈ M_t for every t → no legality assumption on Bob’s outputs; reason: only outcomes with G = 1 contribute to the bound, and they are legal; Remark 6.2 shows the assumption is without loss of generality
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.44, Theorem B.4

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols
import Definitions.Def_FourWayStream_ARHM_Supplement_Simultaneous

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Theorem B.4 (Quantitative simultaneous bound), p.44. Let `N ≥ 2` be even, `m ≥ 1`, `X` uniform
and `M_1, …, M_m` independent draws from a balanced distribution, independent of `X` and of the
encoding randomness; public coins are allowed. Alice sends any `q`-qubit encoding and Bob, who
receives all matchings, decodes jointly. With `p = P[G = 1]` over `X`, the matchings and all coins,
for every integer `s ≥ 1`: `q ≥ s · [p − P[τ_for(M_1, …, M_m) < s]] − h₂(p)`. -/
theorem quantitative_simultaneous_bound (N m : ℕ) (hN : Even N) (hN2 : 2 ≤ N) (hm : 1 ≤ m)
    {Q : Type} [Fintype Q] [DecidableEq Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ)
    (hD : IsBalanced μ D) {nR : ℕ} (P : SimProtocol N m Q nR) (hP : P.Valid)
    (q : ℕ) (hq : P.d ≤ 2 ^ q) (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) * (jointSucc P μ D - listProb (m := m) D (fun qs => tauFor (fun t => μ (qs t)) < s)) -
      binEntropy2 (jointSucc P μ D) ≤ q := by sorry

end FourWayStream.ARHM.Supplement
