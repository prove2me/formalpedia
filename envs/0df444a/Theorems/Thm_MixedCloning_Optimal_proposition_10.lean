-- Prove2me | Theorems.Thm_MixedCloning_Optimal_proposition_10
-- name    : MixedCloning.Optimal.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:27.933355+00:00
-- url     : https://prove2.me/theorems/b4a34556-8696-4351-8b98-a5ad6311e6aa
-- title:
--   Proposition 10 — sample complexity of the PCT cloner
-- statement:
--   Let $1\le r\le d$, $n\ge1$ and $k\ge0$ be integers. Let $R$ be any RPC for these dimensions and $\tau$ any state on the $(n+k)$-copy purification space. The resulting completed PCT map is a channel and, for every state $\rho$ of rank at most $r$,
--
--   $$F(C_{\mathrm{PCT}}(\rho^{\otimes n}),\rho^{\otimes(n+k)})\ge1-\frac{krd}{n}.$$
--
--   For every $\varepsilon>0$, every such $n\ge\lceil krd/\varepsilon\rceil$ therefore attains fidelity at least $1-\varepsilon$. The paper writes $O(krd/\varepsilon)$; its proof yields constant $1$. This is the upper-bound component of sample optimality.
--
--   Differences from the source:
--   - encoding: Werner map on the symmetric subspace → Werner map extended by a fixed output state on the orthogonal complement; reason: the extension is a total channel and agrees with the printed map on random purifications
--   - generalization: the PCT channel specified in Figures 1 and 7 → every channel satisfying the RPC specification and every complementary output state; reason: their action agrees on every tensor-power input, so the printed PCT guarantee follows
--   - encoding: n = O(krd/ε) → every n ≥ 1 with n ≥ ⌈krd/ε⌉, with fidelity ≥ 1−krd/n; reason: the proof on p. 16 supplies the explicit constant 1
--   - generalization: cloning k additional copies with k ≥ 1 → k ≥ 0; reason: the k=0 construction also obeys the printed estimate
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 16, Proposition 10; proof and Figure 7

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem proposition_10 (d r n k : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (hn : 1 ≤ n)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n))
    (hR : IsRPC d r n R) (tau : Op (Word (Fin d × Fin r) (n+k))) (htau : IsState tau) :
    Clones d r n k ((k : ℝ)*r*d/n) (pct d r n k R tau) ∧
    ∀ eps : ℝ, 0 < eps → Nat.ceil ((k : ℝ)*r*d/eps) ≤ n →
      Clones d r n k eps (pct d r n k R tau) := by sorry

end MixedCloning.Optimal
