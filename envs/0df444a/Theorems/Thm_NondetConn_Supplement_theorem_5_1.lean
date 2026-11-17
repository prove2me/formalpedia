-- Prove2me | Theorems.Thm_NondetConn_Supplement_theorem_5_1
-- name    : NondetConn.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:10:52.906437+00:00
-- url     : https://prove2.me/theorems/5b1d06ea-0c84-4a0d-bd68-a80c9391dae6
-- title:
--   Theorem 5.1 — error-dependent randomized lower bound for $\mathsf{bConn}_N$
-- statement:
--   There are absolute constants $c>0$ and $N_0$ such that the following holds uniformly for every error function $\varepsilon:\mathbb N\to\mathbb R$ satisfying $0<\varepsilon(N)<1/3$ on even $N>1$. For every even $N\ge N_0$, every randomized protocol for $\mathsf{bConn}_N$ with worst-case error at most $\varepsilon(N)$ communicates at least
--   $$
--   cN\log_2\!\bigl(\min\{1/\varepsilon(N),N\}\bigr)
--   $$
--   bits in the worst case, regardless of its number of rounds.
--
--   This strengthens the nondeterministic lower bound to weighted, almost monochromatic rectangles and is optimal for polynomially small error.
--
--   Differences from the source:
--   - reading: $R_{\varepsilon}(\mathsf{bConn}_N)=\Omega(N\log(\min(1/\varepsilon,N)))$ for $\varepsilon=\varepsilon(N)$ → one positive constant and one threshold chosen before the entire error function, followed by every even $N$ above the threshold; reason: this is the uniform asymptotic reading required by the theorem's varying-error notation
--   - encoding: randomized protocols with receiver-only output and worst-case communication/error → the published finite communication-tree model with explicit public and private kernels, Alice first, receiver-only correctness, and both outputs checked only when no message is sent; reason: it represents the same finite-input interactive protocols and resolves the source's undefined zero-message receiver without affecting this positive asymptotic bound
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Theorem 5.1, p.14 (PDF p.16)

import Definitions.Def_NondetConn_bConn
import Definitions.Def_NondetConn_Supplement_solves
import Definitions.Def_NondetConn_Supplement_startsWith

set_option autoImplicit false

namespace NondetConn.Supplement

open CommThresholdPR.StrongConverse

/-- **Theorem 5.1** (Zhang, *Settling Nondeterministic Communication Complexity of Graph
Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), printed p.14,
PDF p.16). Uniformly for every error function `ε(N) ∈ (0,1/3)`, any randomized
protocol for `bConn_N` has worst-case communication
`Ω(N log₂(min(1/ε(N),N)))`, without a round bound.

**Formalization Note** The absolute lower-bound constant and threshold precede `ε`, expressing
the theorem's uniformity over error functions. `N` remains the even total number of vertices,
while the published `bConn` takes permutations of `Fin (N/2)`. The public/private-randomness
tree model measures the worst-case number of communicated bits; only the receiver of the last
message must output. -/
theorem theorem_5_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ ε : ℕ → ℝ, (∀ N, 1 < N → Even N → 0 < ε N ∧ ε N < 1 / 3) →
      ∀ N, 1 < N → Even N → N₀ ≤ N →
      ∀ P : Protocol (Equiv.Perm (Fin (N / 2))) (Equiv.Perm (Fin (N / 2))) Bool Bool,
        startsWith P true →
        solves P (fun _ _ ↦ True) (fun a b ↦ decide (NondetConn.bConn (N / 2) a b)) (ε N) →
        c * (N : ℝ) * Real.logb 2 (min (1 / ε N) (N : ℝ)) ≤ (P.cost : ℝ) := by sorry

end NondetConn.Supplement
