-- Prove2me | Theorems.Thm_FourWayStream_ARHM_sequential_joint_success
-- name    : FourWayStream.ARHM.sequential_joint_success
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:26.124201+00:00
-- url     : https://prove2.me/theorems/9b4124b9-ac8e-4a6e-bb26-21a2ad2add28
-- title:
--   Corollary 6.13 — sequential joint success: $q\ge pm-1-m(m^2-1)/(6(N-1))$
-- statement:
--   **Corollary 6.13 (Sequential joint success).** Under the hypotheses of Theorem 6.12, if all $m$ answers are correct with probability at least $p\in[0,1]$, then
--   $$q\ge pm-1-\frac{m(m^2-1)}{6(N-1)}.$$
--   If $m\le\sqrt N$ and $p\ge2/3$, this gives $q\ge m/2-1$, and so $q=\Omega(m)$.
--
--   This is the consumability bound behind the data-first lower bound: answering $m$ fresh sequential Hidden Matching requests needs a message of $\Omega(m)$ qubits up to $m=\sqrt N$.
--
--   Differences from the source:
--   - generalization: requests are perfect matchings M_t ∼ D → requests q_t from a finite set Q drawn from D and naming μ(q_t); reason: Q = perfect matchings, μ = id is the source's setting
--   - encoding: a q-qubit protocol → Alice's message is a density matrix on C^d with d ≤ 2^q; reason: §4.3
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §6.4.1, p.32, Corollary 6.13

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Corollary 6.13 (Sequential joint success), p.32. Under the hypotheses of Theorem 6.12, if all
`m` answers are correct with probability at least `p ∈ [0, 1]`, then
`q ≥ pm − 1 − m(m² − 1)/(6(N − 1))`. If `m ≤ √N` and `p ≥ 2/3`, this gives `q ≥ m/2 − 1`, so
`q = Ω(m)`. -/
theorem sequential_joint_success (N m : ℕ) (hN : Even N) (hN2 : 2 ≤ N) (hm : 1 ≤ m)
    {Q : Type} [Fintype Q] [DecidableEq Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ) (hD : IsBalanced μ D)
    {nR : ℕ} (P : QSeqProtocol N m Q nR) (hP : P.Valid) (hleg : P.LegalOutputs μ)
    (q : ℕ) (hq : P.d ≤ 2 ^ q) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hsucc : p ≤ probOf (P.law D) (fun ω => ∀ t, AnswerCorrect (μ (ω.2.2.1 t)) ω.2.1 (ω.2.2.2 t))) :
    p * m - 1 - m * ((m : ℝ) ^ 2 - 1) / (6 * ((N : ℝ) - 1)) ≤ q ∧
    ((m : ℝ) ≤ Real.sqrt N → 2 / 3 ≤ p → (m : ℝ) / 2 - 1 ≤ q) := by sorry

end FourWayStream.ARHM
