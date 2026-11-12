-- Prove2me | Theorems.Thm_FourWayStream_ARHM_online_forest_growth
-- name    : FourWayStream.ARHM.online_forest_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:48:40.448626+00:00
-- url     : https://prove2.me/theorems/87a0106d-a490-45e4-b858-6ef850c07467
-- title:
--   Lemma 6.10 — online forest growth: $P[\Phi_t=\Phi_{t-1}\mid H_{t-1}]\le\binom t2/(N-1)$
-- statement:
--   **Lemma 6.10 (Online forest growth).** Consider $\mathrm{SeqHM}_{N,m}(D)$ with $N\ge2$ even, $m\ge1$, $X$ uniform, fresh requests and legal outputs, and let $D$ be balanced. Let $e_t\in M_t$ be Bob's answer edge in round $t$, $\Phi_t=\mathrm{fs}(\{e_1,\dots,e_t\})$ with $\Phi_0=0$, and let the history $H_{t-1}$ be the public coins, $M_1,\dots,M_{t-1}$ and the outputs of rounds $1,\dots,t-1$. Then for every $t$ and every value of $H_{t-1}$ with positive probability,
--   $$P[\Phi_t=\Phi_{t-1}\mid H_{t-1}]\le\frac{\binom t2}{N-1}.$$
--   Consequently
--   $$E[\Phi_m]\ge m-\frac{m(m^2-1)}{6(N-1)}.$$
--
--   Fresh requests force the forest of answered edges to grow, whatever edge Bob picks adaptively.
--
--   Differences from the source:
--   - generalization: requests are perfect matchings M_t ∼ D, and H_{t−1} records M_1, …, M_{t−1} → requests q_t from a finite set Q naming μ(q_t), and H_{t−1} records q_1, …, q_{t−1}; reason: Q = perfect matchings, μ = id is the source's setting; conditioning on q is at least as fine as on μ(q)
--   - encoding: freshness (F): M_t is independent of everything that exists before round t → the joint law draws the requests i.i.d. from D independently of X and the coins, and Bob's round-t instrument sees only q_t; reason: this is (F) for the protocol model of the mission
--   - encoding: rounds t = 1, …, m → Φ_t = forest size of the answer edges with 0-based index < t; H_{t−1} keeps the rounds with index + 1 < t; reason: 0-based indices
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §6.4, p.31, Lemma 6.10 (Definition 6.9 with freshness (F), pp.30–31)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Information
import Definitions.Def_FourWayStream_ARHM_Protocols

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Lemma 6.10 (Online forest growth), p.31. In `SeqHM_{N,m}(D)` (`N ≥ 2` even, `m ≥ 1`, `X`
uniform, fresh requests, legal outputs) with `D` balanced, let `Φ_t = fs({e_1, …, e_t})` and
`H_{t−1}` the history before round `t`. For every `t` and every value of `H_{t−1}` with positive
probability, `P[Φ_t = Φ_{t−1} | H_{t−1}] ≤ C(t,2)/(N − 1)`. Consequently
`E[Φ_m] ≥ m − m(m² − 1)/(6(N − 1))`. -/
theorem online_forest_growth (N m : ℕ) (hN : Even N) (hN2 : 2 ≤ N) (hm : 1 ≤ m)
    {Q : Type} [Fintype Q] [DecidableEq Q] (μ : Q → Finset (Sym2 (Fin N))) (D : Q → ℝ) (hD : IsBalanced μ D)
    {nR : ℕ} (P : QSeqProtocol N m Q nR) (hP : P.Valid) (hleg : P.LegalOutputs μ) :
    (∀ t : ℕ, 1 ≤ t → t ≤ m → ∀ ω₀ : QSeqProtocol.Sample N m Q nR,
      0 < probOf (P.law D) (fun ω => QSeqProtocol.history t ω = QSeqProtocol.history t ω₀) →
      condProbOf (P.law D)
          (fun ω => forestSize (outEdges ω.2.2.2 t) = forestSize (outEdges ω.2.2.2 (t - 1)))
          (fun ω => QSeqProtocol.history t ω = QSeqProtocol.history t ω₀) ≤
        (t.choose 2 : ℝ) / ((N : ℝ) - 1)) ∧
    (m : ℝ) - m * ((m : ℝ) ^ 2 - 1) / (6 * ((N : ℝ) - 1)) ≤
      expect (P.law D) (fun ω => (forestSize (outEdges ω.2.2.2 m) : ℝ)) := by sorry

end FourWayStream.ARHM
