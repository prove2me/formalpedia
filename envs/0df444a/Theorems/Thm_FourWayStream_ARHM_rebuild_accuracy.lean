-- Prove2me | Theorems.Thm_FourWayStream_ARHM_rebuild_accuracy
-- name    : FourWayStream.ARHM.rebuild_accuracy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:44:09.84127+00:00
-- url     : https://prove2.me/theorems/d2415adb-b01a-427e-b0bb-8194249a91ca
-- title:
--   Lemma 5.4 — rebuild accuracy: $E[p_{\mathrm{err}}(\kappa)]\le\pi^2/\mu$
-- statement:
--   **Lemma 5.4 (Rebuild accuracy).** Let $\mu\ge1$ and let the stream carry $L=\mu^2$ copies of each of the $N$ coordinates. Fix $x\in\{0,1\}^N$, a perfect matching $M$ of $[N]$, and a set $B$ of $\mu N$ positions in the uniformly random order $\tau$ of the $NL$ labeled updates. Let $\kappa_j$ be the number of updates to coordinate $j$ at the positions of $B$, and let $p_{\mathrm{err}}(\kappa)$ be the probability that measuring $|\phi_\kappa(x)\rangle=N^{-1/2}\sum_j e^{i\pi\kappa_jx_j/\mu}|j\rangle$ in the basis of $M$ returns a wrong parity. Then
--   $$\mathop{E}_{\tau}\big[p_{\mathrm{err}}(\kappa)\big]\le\frac{\pi^2}{\mu}.$$
--
--   This is the accuracy of one register of a ready bank in the random-order algorithm: a register built from one batch answers a request with the wrong parity with probability $O(1/\mu)$.
--
--   Differences from the source:
--   - generalization: µ = 100m with N even and 2 ≤ m ≤ ⌊√N⌋ (§5.1 standing assumptions) → every µ ≥ 1 with L = µ², and every N admitting the perfect matching M; reason: the statement does not involve m; µ = 100m is a special case
--   - encoding: the expectation over the uniformly random order of the NL updates → the average over all bijections τ : Fin (N·µ²) ≃ Fin N × Fin (µ²); reason: uniform distribution on the arrival orders of the labeled updates
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.1, p.20, Lemma 5.4 (state |ϕ_κ(x)⟩ p.20, matching basis p.18)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream
import Definitions.Def_FourWayStream_ARHM_Rebuild

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Lemma 5.4 (Rebuild accuracy), p.20. For `µ ≥ 1` and `L = µ²` copies, fix `x`, a perfect
matching `M` and a set `B` of `µN` positions in the arrival order of the `N L` labeled updates. Let
`κ_j` count the updates to coordinate `j` at those positions and `p_err(κ)` be the probability that
measuring `|ϕ_κ(x)⟩` in the basis of `M` returns a wrong parity. Averaged over the uniformly random
order `τ` of the updates, `E[p_err(κ)] ≤ π²/µ`. -/
theorem rebuild_accuracy (N mu : ℕ) (hmu : 1 ≤ mu) (x : Fin N → Bool)
    (M : Finset (Sym2 (Fin N))) (hM : IsPerfectMatching M)
    (B : Finset (Fin (N * mu ^ 2))) (hB : B.card = mu * N) :
    (∑ τ : Fin (N * mu ^ 2) ≃ Fin N × Fin (mu ^ 2),
        wrongParityProb M x (rebuiltState mu x (batchCounts τ B))) /
      (Fintype.card (Fin (N * mu ^ 2) ≃ Fin N × Fin (mu ^ 2)) : ℝ) ≤ Real.pi ^ 2 / mu := by sorry

end FourWayStream.ARHM
