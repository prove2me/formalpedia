-- Prove2me | Theorems.Thm_OncePaid_Sparse_theorem_4_1
-- name    : OncePaid.Sparse.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:47:41.64971+00:00
-- url     : https://prove2.me/theorems/3b3a6e83-bd99-46d9-90ef-68347177f046
-- title:
--   Theorem 4.1 — sparse fixed-floor separation: $a(C)\ge(85/78)^n/(n+1)^2$, and at most $a(C)(n+1)^2(468/(5e))^n$ successful probes
-- statement:
--   Let $H$ be a simple, $102$-regular bipartite graph with $n>3$ vertices on each side and all nontrivial biadjacency singular values at most $21$. Fix $0<\lambda\le1$, and let $f_H$ be either minimum-weight perfect matching or full minimum-weight edge cover on the price domain $\{2,3,4\}^{E(H)}$. Let $C$ range over min-plus circuits on the edge prices with finite signed constants, positive scalar gates and path-gain floor $\lambda$ (every path from a price input to the output has gain at least $\lambda$).
--
--   1. If $C$ is a sound factor-$(1+\lambda/240)$ approximation, $f_H(c)\le C(c)\le(1+\lambda/240)f_H(c)$ on $\{2,3,4\}^{E(H)}$, then
--
--   $$
--   a(C)\ \ge\ \frac{(85/78)^n}{(n+1)^2}. \tag{4.1}
--   $$
--
--   2. More generally, if $C$ is sound on $\{2,3,4\}^{E(H)}$, then every set $S$ of perfect matchings whose probes satisfy $C(p^M)\le 3n+\lambda n/80$ has $|S|\le a(C)\,(n+1)^2\,(468/(5e))^n$.
--
--   The theorem is the graph-side form of the main separation: on sparse Ramanujan hosts, approximating matching or edge cover on three prices forces exponentially many additions.
--
--   Differences from the source:
--   - encoding: "all nontrivial biadjacency singular values at most 21" → $\|Bf\|_2^2\le21^2\|f\|_2^2$ for every $f\perp\mathbf 1$ on $V_R$; reason: equivalent for a $102$-regular bipartite host.
--   - reading: "at most $a(C)(n+1)^2(468/(5e))^n$ matching probes can satisfy …" → every set $S$ of perfect matchings all of whose probes satisfy the bound has at most that many elements, for every circuit with path floor $\lambda$ sound on $\{2,3,4\}^{E(H)}$; reason: the same statement as a bound on sets; "the whole price domain" is $\{2,3,4\}^{E(H)}$ of the theorem.
--   - encoding: circuits → well-formed straight-line programs, $a(C)$ their addition-gate count, objective values in `WithTop ℝ`, $n$ vertices on each side → $|V_R|=|V_L|=n$; reason: Lean representation.
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 20, Theorem 4.1, Eq. (4.1) (PDF p. 22)

import Mathlib
import Definitions.Def_OncePaid_Sparse_Circuit
import Definitions.Def_OncePaid_Sparse_BipHost

namespace OncePaid.Sparse

/-- Theorem 4.1 (Sparse fixed-floor separation), p. 20. Let `H` be simple, `102`-regular and
bipartite, with `n > 3` vertices on each side and all nontrivial biadjacency singular values at
most `21`. Fix `0 < λ ≤ 1`. For either objective (minimum-weight perfect matching, full
minimum-weight edge cover) on `{2, 3, 4}^{E(H)}`:
(4.1) every well-formed circuit that is a sound factor-`(1 + λ/240)` approximation and has path
floor `λ` satisfies `a(C) ≥ (85/78)^n/(n + 1)²`;
more generally, in every well-formed circuit with path floor `λ` that is sound on the whole price
domain, at most `a(C)(n + 1)²(468/(5e))^n` matching probes satisfy `C(p^M) ≤ 3n + λn/80`. -/
theorem theorem_4_1 {L R : Type} [Fintype L] [Fintype R] (adj : L → R → Prop)
    (hLR : Fintype.card R = Fintype.card L) (hn : 3 < Fintype.card L)
    (hreg : IsBiregular adj 102) (hspec : NontrivialSingularValuesLe adj 21)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (obj : Objective) :
    (∀ C : Circuit (Edge adj), C.WF →
      SoundApprox (1 + lam / 240) (objValue adj obj) C.eval (priceBox (Edge adj)) →
      C.GainFloorOn Set.univ lam →
      (85 / 78 : ℝ) ^ (Fintype.card L) / ((Fintype.card L : ℝ) + 1) ^ 2 ≤ (C.addCount : ℝ)) ∧
    (∀ C : Circuit (Edge adj), C.WF →
      SoundOn (objValue adj obj) C.eval (priceBox (Edge adj)) →
      C.GainFloorOn Set.univ lam →
      ∀ S : Finset (L ≃ R), S ⊆ perfectMatchings adj →
        (∀ M ∈ S, C.eval (probe M) ≤
          3 * (Fintype.card L : ℝ) + lam * (Fintype.card L : ℝ) / 80) →
        (S.card : ℝ) ≤ (C.addCount : ℝ) * ((Fintype.card L : ℝ) + 1) ^ 2 *
          (468 / (5 * Real.exp 1)) ^ (Fintype.card L)) := by sorry

end OncePaid.Sparse
