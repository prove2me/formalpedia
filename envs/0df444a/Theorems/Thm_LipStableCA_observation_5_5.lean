-- Prove2me | Theorems.Thm_LipStableCA_observation_5_5
-- name    : LipStableCA.observation_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:06.365624+00:00
-- url     : https://prove2.me/theorems/1579c0f3-7fd6-452f-a088-0da97a0da834
-- title:
--   Observation 5.5 — the target profiles
-- statement:
--   Fix positive integers $q\le n$ and $k$ with $qk\le m/2$. Let $Y=(Y_1,\dots,Y_q)$ be pairwise disjoint $k$-element subsets of $M$, and let $v^Y_i(Q)=\mathbf 1\{Y_i\subseteq Q\}+|Q|/m$ for $i\le q$ and $v^Y_i=0$ for $i>q$. Then $v^Y_1,\dots,v^Y_q$ are strictly monotone and $\mathrm{OPT}(v^Y)=q+1$. Moreover, every allocation $S$ satisfies
--   $$\sum_{i\in N}v^Y_i(S_i)\le\bigl|\{i\le q:Y_i\subseteq S_i\}\bigr|+1.$$
--
--   These are the hidden-target profiles of the impossibility proof.
--
--   Differences from the source:
--   - encoding: the construction states that $v^Y$ is a profile → validity of $v^Y$ as an extra conclusion; reason: the proof applies the rule at $v^Y$, so this must hold
--   - encoding: $qk\le m/2$ → `2 * (q * k) ≤ m`; reason: same condition over the naturals
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Observation 5.5, p.23

import Definitions.Def_LipStableCA_targetProfile
import Definitions.Def_LipStableCA_Mechanism
open ComplementFreeCA.CFRounding
open Classical

namespace LipStableCA

/-- **Observation 5.5.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.23. **Formalization Note.** validity of `v^Y` as an extra conclusion: the proof applies the rule at `v^Y`, so this must hold. `2 * (q * k) ≤ m`: same condition over the naturals. -/
theorem observation_5_5 {n m q k : ℕ} (hq : 1 ≤ q) (hqn : q ≤ n) (hk : 1 ≤ k) (hqk : 2 * (q * k) ≤ m)
    (Y : Fin q → Finset (Fin m)) (hY : Y ∈ targetTuples q k m) :
    IsProfile (targetProfile Y : Profile n m) ∧
    (∀ i : Fin n, i.val < q → IsStrictlyMonotone ((targetProfile Y : Profile n m) i)) ∧
    opt (targetProfile Y : Profile n m) = (q : ℝ) + 1 ∧
    ∀ S : Alloc n m, welfare (targetProfile Y : Profile n m) S.1 ≤
      ((Finset.univ.filter fun a : Fin q => Y a ⊆ S.1 (Fin.castLE hqn a)).card : ℝ) + 1 := by sorry

end LipStableCA
