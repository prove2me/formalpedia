-- Prove2me | Theorems.Thm_MooreFoelner_treeAct_tPlus_tMinus_and_twoTimes_or_halfTimes
-- name    : MooreFoelner.treeAct_tPlus_tMinus_and_twoTimes_or_halfTimes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T01:06:53.741991+00:00
-- url     : https://prove2.me/theorems/e34e5d19-865e-415f-bbde-14dc41f1a008
-- title:
--   Lemma 5.9 — generators preserve (+) and (−) outside ℰ, so connected sets off ℰ* are uniform
-- statement:
--   If a tree $T$ satisfies $(+)$ and $\gamma \in \Gamma$, then $T \cdot \gamma$ is undefined, in $\mathscr E$, or satisfies $(+)$; the same holds for $(-)$. Consequently, every $\Gamma$-connected set of trees outside $\mathscr E^*$ has all its elements satisfying $(2\times)$ or all satisfying $(\tfrac12\times)$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 16, Lemma 5.9

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem treeAct_tPlus_tMinus_and_twoTimes_or_halfTimes :
    (∀ (T : Finset Seq) (γ : MooreF), IsTree T → TPlus T → γ ∈ gens →
      treeAct T γ = none ∨ ∃ T', treeAct T γ = some T' ∧ (T' ∈ EBad ∨ TPlus T')) ∧
    (∀ (T : Finset Seq) (γ : MooreF), IsTree T → TMinus T → γ ∈ gens →
      treeAct T γ = none ∨ ∃ T', treeAct T γ = some T' ∧ (T' ∈ EBad ∨ TMinus T')) ∧
    ∀ A : Set (Finset Seq), A ⊆ {T | IsTree T} \ EStar → IsConnected treeAct gens A →
      (∀ T ∈ A, TwoTimes T) ∨ ∀ T ∈ A, HalfTimes T := by
  sorry

end MooreFoelner
