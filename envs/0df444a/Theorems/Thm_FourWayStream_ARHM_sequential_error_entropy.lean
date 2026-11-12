-- Prove2me | Theorems.Thm_FourWayStream_ARHM_sequential_error_entropy
-- name    : FourWayStream.ARHM.sequential_error_entropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:41.796953+00:00
-- url     : https://prove2.me/theorems/e43c82e2-0634-4dc5-b95e-2d0dcc013069
-- title:
--   Theorem 6.12 — sequential error-entropy bound
-- statement:
--   **Theorem 6.12 (Sequential error-entropy bound).** For balanced $D$, uniform $X$ and fresh requests ($N\ge2$ even, $m\ge1$, legal outputs), every $q$-qubit protocol for $\mathrm{SeqHM}_{N,m}(D)$ satisfies
--   $$q\ge m-\frac{m(m^2-1)}{6(N-1)}-H(Z\mid O,M)\ge m-\frac{m(m^2-1)}{6(N-1)}-H(Z),$$
--   where $Z$ is the error vector.
--
--   It combines online forest growth with sequential forest information into a bound in terms of the entropy of the errors.
--
--   Differences from the source:
--   - generalization: requests are perfect matchings M_t ∼ D → requests q_t from a finite set Q drawn from D and naming μ(q_t); reason: Q = perfect matchings, μ = id is the source's setting
--   - encoding: Z_t = b_t ⊕ X_{u_t} ⊕ X_{v_t} → errVec, with Z_t := false on a missing answer; reason: legal outputs never miss, so the convention changes no instance
--   - encoding: a q-qubit protocol → Alice's message is a density matrix on C^d with d ≤ 2^q; reason: §4.3
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §6.4.1, p.32, Theorem 6.12

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Theorem 6.12 (Sequential error-entropy bound), p.32. For balanced `D`, uniform `X` and fresh
requests (`N ≥ 2` even, `m ≥ 1`, legal outputs), every protocol for `SeqHM_{N,m}(D)` whose message
has `q` qubits satisfies
`q ≥ m − m(m² − 1)/(6(N − 1)) − H(Z | O, M) ≥ m − m(m² − 1)/(6(N − 1)) − H(Z)`. -/
theorem sequential_error_entropy (N m : ℕ) (hN : Even N) (hN2 : 2 ≤ N) (hm : 1 ≤ m)
    {Q : Type} [Fintype Q] [DecidableEq Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ) (hD : IsBalanced μ D)
    {nR : ℕ} (P : QSeqProtocol N m Q nR) (hP : P.Valid) (hleg : P.LegalOutputs μ)
    (q : ℕ) (hq : P.d ≤ 2 ^ q) :
    (m : ℝ) - m * ((m : ℝ) ^ 2 - 1) / (6 * ((N : ℝ) - 1)) -
        condEntropyOf (P.law D) (fun ω => errVec ω.2.1 ω.2.2.2) (fun ω => (ω.2.2.2, ω.2.2.1)) ≤ q ∧
    (m : ℝ) - m * ((m : ℝ) ^ 2 - 1) / (6 * ((N : ℝ) - 1)) -
        entropyOf (P.law D) (fun ω => errVec ω.2.1 ω.2.2.2) ≤
      (m : ℝ) - m * ((m : ℝ) ^ 2 - 1) / (6 * ((N : ℝ) - 1)) -
        condEntropyOf (P.law D) (fun ω => errVec ω.2.1 ω.2.2.2) (fun ω => (ω.2.2.2, ω.2.2.1)) := by sorry

end FourWayStream.ARHM
