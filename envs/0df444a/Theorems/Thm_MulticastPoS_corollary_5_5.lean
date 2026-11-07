-- Prove2me | Theorems.Thm_MulticastPoS_corollary_5_5
-- name    : MulticastPoS.corollary_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:45.818767+00:00
-- url     : https://prove2.me/theorems/804d2b39-b327-457b-91d7-86f9d8d1f6f5
-- title:
--   Corollary 5.5 — expected contribution of copied tails: $\mathbb EH_{D_e}\le H_{x_e}$, and $\le\frac12H_{x_e}$ if $x_e<K$
-- statement:
--   In the setting of Lemma 5.3 (an integer $K\ge 4$, nonresidual groups with at least $4K$ members, representatives chosen uniformly and independently), the copied tails satisfy
--
--   $$
--   \mathbb E H_{D_e}\le H_{x_e}\quad\text{for every } e\in T, \tag{16}
--   $$
--
--   $$
--   \mathbb E H_{D_e}\le \tfrac12 H_{x_e}\quad\text{for every } e\in T \text{ with } 1\le x_e<K. \tag{17}
--   $$
--
--   Here $T=\operatorname{supp}(P)$, so $e\in T$ means $x_e\ge 1$. The second bound is the saving that Lemma 3.2 subtracts from $\Phi(P)$.
--
--   Differences from the source:
--   - generalization: P the fixed tree-supported global potential minimizer, e ∈ T = supp(P) → any family of edge sets P : ι → Finset (Sym2 V), every edge e; reason: the proof uses only that x_e counts the players whose set contains e; for e ∉ T both sides vanish
--   - encoding: source occurrences o_i with locations ℓ(o_i) = s_i, groups of occurrences → players i ∈ ι with sources s i, groups as Finsets of players; reason: occurrences are in bijection with players (p.4)
--   - encoding: E and Pr over representatives chosen uniformly at random in each nonresidual group, independently across groups → uniform average over the finite type Selection π g₀ of representative choices; reason: independent uniform choices are the uniform distribution on the product of the groups
--   - generalization: the groups of Lemma 4.1 with Q = 4K on T⋆ → any partition of the players with an optional residual group whose nonresidual groups have at least 4K members; reason: only the lower size bound of the nonresidual groups is used
--   - encoding: e ∈ T → 1 ≤ load P e; reason: T = supp(P) is the set of edges with positive load
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Corollary 5.5, p.12 (PDF p.13), Eqs. (16)–(17)

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_MulticastPoS_tailCount
import Definitions.Def_NoSignalPA_uniformExp

open CongestionPoA.AsymSum

namespace MulticastPoS

/-- Corollary 5.5, expected contribution of copied tails (Huang–Yuan, *An O(log log n) Upper
Bound on the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission
manuscript (sha256 dd0e08d0…f6d4), p.12): in the setting of Lemma 5.3 (nonresidual groups of
size at least `4K`, `K ≥ 4`, representatives chosen uniformly and independently),
`E H_{D_e} ≤ H_{x_e}` for every edge `e` of `T` (16), and `E H_{D_e} ≤ ½ H_{x_e}` for every
edge `e` of `T` with `1 ≤ x_e < K` (17).

**Formalization Note** "`e ∈ T`" for `T = supp(P)` is `1 ≤ x_e`. Expectations are uniform
averages over representative selections (the published `NoSignalPA.uniformExp`). The paper's
`P` is the tree-supported global minimizer; the statement covers every family of edge sets `P`. -/
theorem corollary_5_5 {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (P : ι → Finset (Sym2 V)) (π : Finpartition (Finset.univ : Finset ι))
    (g₀ : Option (Finset ι)) (K : ℕ) (hK : 4 ≤ K)
    (hsize : ∀ g ∈ nonresidual π g₀, 4 * K ≤ g.card) :
    (∀ e, 1 ≤ load P e →
      NoSignalPA.uniformExp
          (fun σ : Selection π g₀ => (harmonic (tailCount P σ e) : ℝ)) ≤
        harmonic (load P e)) ∧
    (∀ e, 1 ≤ load P e → load P e < K →
      NoSignalPA.uniformExp
          (fun σ : Selection π g₀ => (harmonic (tailCount P σ e) : ℝ)) ≤
        (harmonic (load P e) : ℝ) / 2) := by sorry

end MulticastPoS
