-- Prove2me | Theorems.Thm_MulticastPoS_lemma_5_3
-- name    : MulticastPoS.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:31.1326+00:00
-- url     : https://prove2.me/theorems/2a37e40c-4a0d-4d82-be86-cd8cb82dff1f
-- title:
--   Lemma 5.3 — copied-tail counts: $D_e\in\{0\}\cup[4K,\infty)$, $\mathbb ED_e\le x_e$, $\Pr[D_e>0]\le x_e/(4K)$
-- statement:
--   Let $K\ge 4$ be an integer and let the players be partitioned into groups, every nonresidual group having at least $4K$ members. Choose one representative in each nonresidual group uniformly at random, independently across groups, and let $D_e$ be the copied-tail count of edge $e$ for a profile $P$ with loads $x_e$. Then $D_e$ is either zero or at least $4K$, and
--
--   $$
--   \mathbb E D_e\le x_e,\qquad \Pr[D_e>0]\le\frac{x_e}{4K}. \tag{11}
--   $$
--
--   The probability bound shows that edges with few users are rarely copied.
--
--   Differences from the source:
--   - generalization: P the fixed tree-supported global potential minimizer, e ∈ T = supp(P) → any family of edge sets P : ι → Finset (Sym2 V), every edge e; reason: the proof uses only that x_e counts the players whose set contains e; for e ∉ T both sides vanish
--   - encoding: source occurrences o_i with locations ℓ(o_i) = s_i, groups of occurrences → players i ∈ ι with sources s i, groups as Finsets of players; reason: occurrences are in bijection with players (p.4)
--   - encoding: E and Pr over representatives chosen uniformly at random in each nonresidual group, independently across groups → uniform average over the finite type Selection π g₀ of representative choices; reason: independent uniform choices are the uniform distribution on the product of the groups
--   - generalization: the groups of Lemma 4.1 with Q = 4K on T⋆ → any partition of the players with an optional residual group whose nonresidual groups have at least 4K members; reason: the proof uses only the lower size bound Q = 4K ≤ |g| of the nonresidual groups
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Lemma 5.3, p.11 (PDF p.12), Eq. (11)

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_MulticastPoS_tailCount
import Definitions.Def_NoSignalPA_uniformExp

open CongestionPoA.AsymSum

namespace MulticastPoS

/-- Lemma 5.3, copied-tail counts (Huang–Yuan, *An O(log log n) Upper Bound on the Price of
Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256
dd0e08d0…f6d4), p.11, Eq. (11)): let the players be partitioned into groups, every nonresidual
group having at least `Q = 4K` members (`K ≥ 4`), and choose one representative per nonresidual
group uniformly and independently. Then for every edge `e`, `D_e` is either zero or at least
`4K`, and
`E D_e ≤ x_e`, `Pr[D_e > 0] ≤ x_e / (4K)`,
where `x_e` is the load of `e` in the profile `P` whose paths are copied.

**Formalization Note** The expectation is the uniform average over representative selections
(the published `NoSignalPA.uniformExp`), and `Pr[D_e > 0]` the average of the indicator. The
paper states this for the tree-supported global minimizer `P` and `e ∈ T`; the statement
covers every family of edge sets `P` and every edge (for `e ∉ T` both sides vanish). Only the
lower size bound of the nonresidual groups is assumed. -/
theorem lemma_5_3 {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (P : ι → Finset (Sym2 V)) (π : Finpartition (Finset.univ : Finset ι))
    (g₀ : Option (Finset ι)) (K : ℕ) (hK : 4 ≤ K)
    (hsize : ∀ g ∈ nonresidual π g₀, 4 * K ≤ g.card) (e : Sym2 V) :
    (∀ σ : Selection π g₀, tailCount P σ e = 0 ∨ 4 * K ≤ tailCount P σ e) ∧
    NoSignalPA.uniformExp (fun σ : Selection π g₀ => (tailCount P σ e : ℝ)) ≤ load P e ∧
    NoSignalPA.uniformExp
        (fun σ : Selection π g₀ => if 0 < tailCount P σ e then (1 : ℝ) else 0) ≤
      (load P e : ℝ) / (4 * K) := by sorry

end MulticastPoS
