-- Prove2me | Theorems.Thm_MixedCloning_Optimal_pct_isChannel
-- name    : MixedCloning.Optimal.pct_isChannel
-- status  : Proved
-- author  : @dmitry
-- created : 2026-11-22T02:08:26.335691+00:00
-- url     : https://prove2.me/theorems/bfede41e-1876-4676-a7c2-4578b7215644
-- title:
--   Figure 7 — the completed PCT map is a quantum channel
-- statement:
--   Fix integers $d,r\ge1$ and $n,k\ge0$, and put $D=dr$. Let $R$ be any quantum channel from $(\mathbb C^d)^{\otimes n}$ to $(\mathbb C^d\otimes\mathbb C^r)^{\otimes n}$, and let $\tau$ be any state on $(\mathbb C^d\otimes\mathbb C^r)^{\otimes(n+k)}$. Write $\Pi_j$ for the projector onto the symmetric subspace of $(\mathbb C^D)^{\otimes j}$ and $D[j]=\binom{j+D-1}{j}$ for its dimension. The completed Werner map is
--
--   $$
--   \mathcal C_W(X)=\frac{D[n]}{D[n+k]}\,\Pi_{n+k}\big(\Pi_nX\Pi_n\otimes I^{\otimes k}\big)\Pi_{n+k}+\operatorname{tr}\big((I-\Pi_n)X\big)\,\tau .
--   $$
--
--   Then the purify–clone–trace map
--
--   $$
--   \mathcal C_{\mathrm{PCT}}(X)=\operatorname{tr}_{B_1\cdots B_{n+k}}\Big(\mathcal C_W\big(R(X)\big)\Big)
--   $$
--
--   is a quantum channel, that is, a linear, completely positive, trace-preserving map admitting a normalized Kraus family.
--
--   This is the channel part of the PCT cloner of Figure 7: it is the composition of the random purification channel, Werner's cloner on $\mathbb C^D$, and the partial trace over the auxiliary registers. It supplies the channel requirement in Proposition 10.
--
--   **Formalization Note** The PCT map is the platform function `pct d r n k R τ`. Werner's map is completed by $\tau$ off the symmetric input corner, so that it is a total channel; on symmetric inputs, in particular on tensor powers of pure states, the second term vanishes.
--
--   Differences from the source:
--   - encoding: Werner's map on the symmetric subspace → Werner's map completed by a fixed state $\tau$ on the orthogonal complement; reason: the completed map is a total channel and agrees with the printed map on random purifications
--   - generalization: the random purification channel → any channel $R$ of the right shape; reason: only the channel property of $R$ is needed for the composition to be a channel
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/243.pdf, p. 15, Figure 7 (PCT cloner: apply RPC(d,r,n), then Werner's cloner C_W^(D,n,k), then trace out B); used for the channel requirement of Proposition 10 (p. 16).

import Definitions.Def_MixedCloning_Optimal_Model

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Figure 7 (PDF p.15): purify, apply the completed Werner map, trace out B. For any channel
`R` and any state `tau` completing Werner's map off the symmetric corner, the PCT map is a channel. -/
theorem pct_isChannel (d r n k : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n)) (hR : QAlgorithms.IsChannel R)
    (tau : Op (Word (Fin d × Fin r) (n+k))) (htau : IsState tau) :
    QAlgorithms.IsChannel (pct d r n k R tau) := by sorry

end MixedCloning.Optimal
