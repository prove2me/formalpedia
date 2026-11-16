-- Prove2me | Theorems.Thm_MixedCloning_Optimal_Supplement_proposition_25
-- name    : MixedCloning.Optimal.Supplement.proposition_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:16:13.711079+00:00
-- url     : https://prove2.me/theorems/dcb27bf6-2765-4648-9482-c902ac1765c4
-- title:
--   Proposition 25 — sample complexity of the PTT transposer
-- statement:
--   Let $1\le r\le d$, $n\ge1$ and $k\ge0$ be integers. Let $R$ be any channel meeting the random purification channel specification RPC$^{(d,r,n)}$, and $\tau$ any state on $k$ registers of $\mathbb C^d\otimes\mathbb C^r$. The PTT transposer $\mathrm{PTT}=\mathrm{Tr}_B\circ T^{(dr,n,k)}\circ R$ is a channel and, for every state $\rho$ on $\mathbb C^d$ of rank at most $r$,
--
--   $$F\bigl(\mathrm{PTT}(\rho^{\otimes n}),(\rho^{\mathsf T})^{\otimes k}\bigr)\ge1-\frac{krd}{n}.$$
--
--   Consequently, for every $\varepsilon>0$, every $n\ge\lceil krd/\varepsilon\rceil$ gives fidelity at least $1-\varepsilon$. The paper writes $n=O(krd/\varepsilon)$; its proof (p. 27, last line) yields constant $1$. This is the upper-bound half of Theorem 27.
--
--   **Formalization Note** $F$ is the squared fidelity. The transpose is taken in the computational basis of $\mathbb C^d$ (p. 26).
--
--   Differences from the source:
--   - reading: the optimal pure-state transposer $T^{(D,n,k)}$ of [BGSQ26], given without a formula → the complementary channel of Werner's cloner, $X\mapsto \frac{D[n]}{D[n+k]}(\mathrm{Tr}_{1..n}[\Pi_{n+k}(\Pi_nX\Pi_n\otimes I^{\otimes k})])^{\mathsf T}$ on the symmetric corner; reason: p. 8 identifies the optimal pure-state transposer with the complement of Werner's cloner
--   - encoding: the pure-state transposer on the symmetric subspace → extended by a fixed output state $\tau$ on the orthogonal complement; reason: the extension is a total channel and agrees with the printed map on random purifications, whose outputs are symmetric
--   - generalization: the PTT transposer of Figure 8 → every channel satisfying the RPC specification and every complementary output state $\tau$; reason: all of them agree on tensor-power inputs of rank at most r, so the printed PTT is one instance
--   - encoding: $n=O(krd/\varepsilon)$ → every $n\ge1$ with fidelity $\ge1-krd/n$, and every $n\ge\lceil krd/\varepsilon\rceil$ for $\varepsilon>0$; reason: the proof on p. 27 supplies the explicit constant 1
--   - reading: a mixed state $\rho$ → a state of rank at most $r$; reason: the PTT transposer is built for rank-r inputs (p. 26), and rank at most r is the stronger reading
--   - generalization: $k\ge1$ copies → $k\ge0$; reason: the k = 0 case also obeys the printed estimate, and k ≥ 1 is a special case
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 27, Proposition 25 and its proof; Figure 8 on p. 26

import Definitions.Def_MixedCloning_Optimal_Supplement_Transposition

noncomputable section
open Matrix MixedCloning.Optimal
open scoped Matrix ComplexConjugate

namespace MixedCloning.Optimal.Supplement
attribute [local instance] Classical.propDecidable Classical.decEq

theorem proposition_25 (d r n k : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (hn : 1 ≤ n)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n))
    (hR : IsRPC d r n R) (tau : Op (Word (Fin d × Fin r) k)) (htau : IsState tau) :
    Transposes d r n k ((k : ℝ)*r*d/n) (ptt d r n k R tau) ∧
    ∀ eps : ℝ, 0 < eps → Nat.ceil ((k : ℝ)*r*d/eps) ≤ n →
      Transposes d r n k eps (ptt d r n k R tau) := by sorry

end MixedCloning.Optimal.Supplement
