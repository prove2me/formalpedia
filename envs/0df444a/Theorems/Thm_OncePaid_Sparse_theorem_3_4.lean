-- Prove2me | Theorems.Thm_OncePaid_Sparse_theorem_3_4
-- name    : OncePaid.Sparse.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:47:25.744653+00:00
-- url     : https://prove2.me/theorems/58c54b4f-9715-4251-9f68-c8cd46cfa445
-- title:
--   Theorem 3.4 — successful matching probes number at most $a(C)(n+1)^2B_H(2b/\lambda)$
-- statement:
--   Let $H$ be a bipartite host with $n>3$ vertices on each side, and let $f_H$ be either minimum-weight perfect matching or full minimum-weight edge cover. Let $C$ be a min-plus circuit over the edge prices, with finite signed constants and positive scalar gates, that is sound for $f_H$ on $\{2,3,4\}^E$ (that is, $f_H(c)\le C(c)$ there), and suppose every path from a price input to the output has gain at least $\lambda>0$. If $0\le b<n/3$ and $S\subseteq\mathcal M(H)$ is a set of perfect matchings with $C(p^M)\le 3n+b$ for every $M\in S$, then
--
--   $$
--   |S|\ \le\ a(C)\,(n+1)^2\,B_H(2b/\lambda). \tag{3.6}
--   $$
--
--   Here $p^M$ is the probe with price 3 on $M$ and 4 elsewhere, $a(C)$ the number of addition gates and $B_H$ the cut count (3.5). The theorem separates the circuit argument from the graph count: any bound on $B_H$ turns a large number of successful probes into many addition gates.
--
--   Differences from the source:
--   - encoding: $B_H(\tau)$ is defined for $n>3$ → hypothesis $3<n$; reason: the definition domain of $B_H$ in (3.5), which the statement uses.
--   - encoding: $n$ vertices on each side → hypothesis $|V_R|=|V_L|$, $n=|V_L|$; reason: standing assumption of §3.2.
--   - generalization: §3.2's standing assumption that $H$ has at least one perfect matching → not assumed; reason: without a perfect matching $S=\emptyset$ and the bound is trivial, so the statement specializes to the source's.
--   - encoding: circuit with positive scalar gates and gain floor on every price-input path → well-formed straight-line program (`Circuit.WF`) with `GainFloorOn Set.univ λ`; $a(C)$ counts the addition gates of the program; reason: Lean representation of the shared DAG.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 14, Theorem 3.4, Eq. (3.6) (PDF p. 16)

import Mathlib
import Definitions.Def_OncePaid_Sparse_Circuit
import Definitions.Def_OncePaid_Sparse_BipHost

namespace OncePaid.Sparse

/-- Theorem 3.4 (Cut concentration bounds successful probes), p. 14. Let `H` be a bipartite host
with `n > 3` vertices on each side, `obj` either objective, and `C` a well-formed min-plus
circuit over the edge prices (finite signed constants, positive scalar gates) that is sound for
`f_H` on `{2, 3, 4}^E`, with gain at least `λ > 0` on every path from a price input to the
output. If `0 ≤ b < n/3` and `S ⊆ M(H)` satisfies `C(p^M) ≤ 3n + b` for every `M ∈ S`, then
`|S| ≤ a(C) (n + 1)² B_H(2b/λ)` (3.6). -/
theorem theorem_3_4 {L R : Type} [Fintype L] [Fintype R] (adj : L → R → Prop)
    (hLR : Fintype.card R = Fintype.card L) (hn : 3 < Fintype.card L) (obj : Objective)
    (C : Circuit (Edge adj)) (hC : C.WF)
    (hsound : SoundOn (objValue adj obj) C.eval (priceBox (Edge adj)))
    (lam : ℝ) (hlam : 0 < lam) (hgain : C.GainFloorOn Set.univ lam)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b < (Fintype.card L : ℝ) / 3)
    (S : Finset (L ≃ R)) (hS : S ⊆ perfectMatchings adj)
    (hprobe : ∀ M ∈ S, C.eval (probe M) ≤ 3 * (Fintype.card L : ℝ) + b) :
    (S.card : ℝ) ≤
      (C.addCount : ℝ) * ((Fintype.card L : ℝ) + 1) ^ 2 * (cutCount adj (2 * b / lam) : ℝ) := by sorry

end OncePaid.Sparse
