-- Prove2me | Theorems.Thm_FourWayStream_ARHM_sequential_forest_information
-- name    : FourWayStream.ARHM.sequential_forest_information
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:40.432664+00:00
-- url     : https://prove2.me/theorems/5749f041-1224-45a5-8c75-95b028a8f022
-- title:
--   Lemma 6.11 — sequential forest information: $q\ge E[\Phi_m]-H(Z\mid O,M)$
-- statement:
--   **Lemma 6.11 (Sequential forest information).** Consider $\mathrm{SeqHM}_{N,m}(D)$ with $N\ge2$ even, $m\ge1$, $X$ uniform, requests drawn independently from a distribution $D$ on perfect matchings, and legal outputs. Let $\Phi_m=\mathrm{fs}(\{e_1,\dots,e_m\})$ and let $Z=(Z_1,\dots,Z_m)$ with $Z_t=b_t\oplus X_{u_t}\oplus X_{v_t}$ be the error vector. Every $q$-qubit protocol satisfies
--   $$q\ge E[\Phi_m]-H(Z\mid O,M)\ge E[\Phi_m]-H(Z).$$
--
--   Knowing $Z$ repairs every reported parity, so the whole forest of answers counts, at the price of describing the errors.
--
--   Differences from the source:
--   - generalization: requests are perfect matchings M_t ∼ D → requests q_t from a finite set Q drawn from D and naming μ(q_t); reason: Q = perfect matchings, μ = id is the source's setting
--   - encoding: Z_t = b_t ⊕ X_{u_t} ⊕ X_{v_t} → errVec, with Z_t := false on a missing answer; reason: legal outputs never miss, so the convention changes no instance
--   - encoding: a q-qubit protocol → Alice's message is a density matrix on C^d with d ≤ 2^q; reason: §4.3
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §6.4.1, p.31, Lemma 6.11

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Lemma 6.11 (Sequential forest information), p.31. In `SeqHM_{N,m}(D)` (`N ≥ 2` even, `m ≥ 1`,
`X` uniform, requests i.i.d. from a distribution `D` on perfect matchings, legal outputs), every
protocol whose message has `q` qubits satisfies `q ≥ E[Φ_m] − H(Z | O, M) ≥ E[Φ_m] − H(Z)`, where
`Φ_m = fs({e_1, …, e_m})` and `Z_t = b_t ⊕ X_{u_t} ⊕ X_{v_t}` is the error vector. -/
theorem sequential_forest_information (N m : ℕ) (hN : Even N) (hN2 : 2 ≤ N) (hm : 1 ≤ m)
    {Q : Type} [Fintype Q] [DecidableEq Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ) (hD : IsMatchingDist μ D)
    {nR : ℕ} (P : QSeqProtocol N m Q nR) (hP : P.Valid) (hleg : P.LegalOutputs μ)
    (q : ℕ) (hq : P.d ≤ 2 ^ q) :
    expect (P.law D) (fun ω => (forestSize (outEdges ω.2.2.2 m) : ℝ)) -
        condEntropyOf (P.law D) (fun ω => errVec ω.2.1 ω.2.2.2) (fun ω => (ω.2.2.2, ω.2.2.1)) ≤ q ∧
    expect (P.law D) (fun ω => (forestSize (outEdges ω.2.2.2 m) : ℝ)) -
        entropyOf (P.law D) (fun ω => errVec ω.2.1 ω.2.2.2) ≤
      expect (P.law D) (fun ω => (forestSize (outEdges ω.2.2.2 m) : ℝ)) -
        condEntropyOf (P.law D) (fun ω => errVec ω.2.1 ω.2.2.2) (fun ω => (ω.2.2.2, ω.2.2.1)) := by sorry

end FourWayStream.ARHM
