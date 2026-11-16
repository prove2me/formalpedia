-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_forest_information_bound
-- name    : FourWayStream.ARHM.Supplement.forest_information_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:02:46.782352+00:00
-- url     : https://prove2.me/theorems/661e353c-a591-474c-95d5-d1dd56b31278
-- title:
--   Lemma 6.6 — forest-information bound $q\ge I(X:O\mid M)\ge\mathbb E[G\,\mathrm{fs}(\{e_1,\dots,e_m\})]-h_2(p)$
-- statement:
--   Let $N\ge2$ be even, $m\ge1$, $X$ uniform on $\{0,1\}^N$, and $M=(M_1,\dots,M_m)$ i.i.d. from a distribution $D$ on perfect matchings of $[N]$, independent of $X$ and of the public coins. Consider any one-way protocol for $\mathrm{MHM}_{N,m}$ whose message has $q$ qubits, with Bob's output $O=((e_1,b_1),\dots,(e_m,b_m))$, $G$ the indicator that all $m$ answers are correct, and $p=\mathbb P[G=1]$. Then
--   $$q\ \ge\ I(X:O\mid M)\ \ge\ \mathbb E\big[G\,\mathrm{fs}(\{e_1,\dots,e_m\})\big]-h_2(p),$$
--   where $\mathrm{fs}$ is the forest size and $h_2$ the binary entropy in bits.
--
--   The forest Bob selects may depend on whether he succeeds, which is why the bound carries the product $G\,\mathrm{fs}$ and not $p\,\mathbb E[\mathrm{fs}]$. It is the information step of Theorems B.4 and 6.7.
--
--   **Formalization Note** Entropies and mutual information are Shannon quantities in bits on the finite joint law of (coins, $X$, $M$, $O$); $\{e_1,\dots,e_m\}$ is the set of edges of the answers.
--
--   Differences from the source:
--   - encoding: a message of q qubits (classical information included) → a density matrix on C^d with d ≤ 2^q; reason: §4.3 defines q qubits as dimension at most 2^q; same protocols
--   - encoding: a distribution D on perfect matchings of [N] → a distribution on a finite request type Q, request q naming the perfect matching μ(q); reason: Lean convention; with Q the perfect matchings and μ = id it is the source distribution
--   - generalization: Remark 6.2: outputs are legal, e_t ∈ M_t for every t → no legality assumption on Bob’s outputs; reason: on the event G = 1 every answer is a legal edge, so the bound does not use the assumption; Remark 6.2 shows it is without loss of generality
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.29, Lemma 6.6 (proof p.30)

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

/-- Lemma 6.6 (Forest-information bound), p.29. In `MHM_{N,m}` (`N ≥ 2` even, `m ≥ 1`, `X` uniform,
the matchings i.i.d. from a distribution `D` on perfect matchings, independent of `X` and the coins),
for every one-way protocol whose message has `q` qubits (dimension at most `2^q`), with
`{e_1, …, e_m}` the set of edges of Bob's output `O`, `G` the indicator that all answers are correct
and `p = P[G = 1]`: `q ≥ I(X : O | M) ≥ E[G · fs({e_1, …, e_m})] − h₂(p)`. -/
theorem forest_information_bound (N m : ℕ) (hN : Even N) (hN2 : 2 ≤ N) (hm : 1 ≤ m)
    {Q : Type} [Fintype Q] [DecidableEq Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ)
    (hD : IsMatchingDist μ D) {nR : ℕ} (P : SimProtocol N m Q nR) (hP : P.Valid)
    (q : ℕ) (hq : P.d ≤ 2 ^ q) :
    condMutualInfoOf (simLaw P D) (fun ω => ω.2.1) (fun ω => ω.2.2.2) (fun ω => ω.2.2.1) ≤ q ∧
    expect (simLaw P D) (fun ω => if allCorrect μ ω then
        (forestSize (selEdges ω.2.2.2 Finset.univ) : ℝ) else 0) -
        binEntropy2 (jointSucc P μ D) ≤
      condMutualInfoOf (simLaw P D) (fun ω => ω.2.1) (fun ω => ω.2.2.2) (fun ω => ω.2.2.1) := by sorry

end FourWayStream.ARHM.Supplement
