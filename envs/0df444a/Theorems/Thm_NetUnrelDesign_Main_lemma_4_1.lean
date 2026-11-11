-- Prove2me | Theorems.Thm_NetUnrelDesign_Main_lemma_4_1
-- name    : NetUnrelDesign.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:09:29.312347+00:00
-- url     : https://prove2.me/theorems/28d082d7-cef5-4f69-8056-e3bfad8c2708
-- title:
--   Lemma 4.1 — cut count and overcount: ≤ n^{2t/λ} cuts of weight ≤ t; (4.1) tail and (4.2) 0 ≤ z/u − 1 ≤ n³e^{−λ/2}
-- statement:
--   Let $G$ be the paper's connected multigraph on $n\ge2$ vertices, with nonnegative edge weights $w$. Edges fail independently with probability $e^{-w_e}$. Cuts are nontrivial bipartitions of the vertices with the two shores identified, $w(C)$ is the weight of the edges crossing $C$, $\lambda=\min_Cw(C)$, $z=\sum_Ce^{-w(C)}$, and $u$ is the disconnection probability. Let $\lambda>0$. For $t\ge\lambda$, the number of cuts of weight at most $t$ is at most $n^{2t/\lambda}$. If $\lambda\ge4\log n$, then for every $\alpha\ge1$
--   $$\sum_{C:\,w(C)>\alpha\lambda}e^{-w(C)}\le2n^{2\alpha}e^{-\alpha\lambda},\tag{4.1}$$
--   $$0\le z/u-1\le n^3e^{-\lambda/2}.\tag{4.2}$$
--   The first clause is Karger's cut-counting bound, posed on Prove2Me as the Open `RandDelMatroid.Indep.theorem_4`; here it is part of the lemma as a whole.
--
--   Differences from the source:
--
--   - encoding: G is the paper's network (standing assumption of §1: connected, n ≥ 2) → hypotheses 2 ≤ n and IsConnectedGraph ends; reason: the paper's graph always satisfies them; no instance of the source is excluded
--   - encoding: cuts as nontrivial bipartitions with shores identified; n^{2t/λ} → Sym2 pairs s(S, Sᶜ) with S nonempty and S ≠ V (each cut once); real power (n : ℝ)^(2t/λ); reason: same objects
-- source:
--   Sun 2026, Fast Approximation Algorithms for Minimizing Network Unreliability, doi:10.5281/zenodo.23914978 (PDF sha256 1120f100…), Lemma 4.1, p. 12 (PDF 13)

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model

open scoped BigOperators Classical

namespace NetUnrelDesign.Main

/-- **Lemma 4.1 (Cut count and overcount).** For the connected multigraph `G` (`n ≥ 2`) with
nonnegative edge weights `w` (edges failing independently with probability `e^{−w_e}`), let
`λ = min_C w(C) > 0`, where cuts are nontrivial bipartitions with shores identified. For `t ≥ λ`
the number of cuts of weight at most `t` is at most `n^{2t/λ}`. If `λ ≥ 4 log n`, then for every
`α ≥ 1`, (4.1) `Σ_{C : w(C) > αλ} e^{−w(C)} ≤ 2 n^{2α} e^{−αλ}`, and (4.2)
`0 ≤ z/u − 1 ≤ n³ e^{−λ/2}` with `z = Σ_C e^{−w(C)}`. Sun 2026, p. 12 (PDF 13). -/
theorem lemma_4_1 {n m : ℕ} (ends : Ends n m) (hn : 2 ≤ n) (hconn : IsConnectedGraph ends)
    (w : Fin m → ℝ) (hw : ∀ e, 0 ≤ w e) (hlam : 0 < minCut ends w) :
    (∀ t : ℝ, minCut ends w ≤ t →
      ((((cuts n).filter fun C => cutWeight ends w C ≤ t).card : ℕ) : ℝ) ≤
        (n : ℝ) ^ (2 * t / minCut ends w)) ∧
    (4 * Real.log n ≤ minCut ends w →
      (∀ α : ℝ, 1 ≤ α →
        ∑ C ∈ (cuts n).filter (fun C => α * minCut ends w < cutWeight ends w C),
            Real.exp (-cutWeight ends w C) ≤
          2 * (n : ℝ) ^ (2 * α) * Real.exp (-(α * minCut ends w))) ∧
      0 ≤ cutSum ends w / unrelW ends w - 1 ∧
      cutSum ends w / unrelW ends w - 1 ≤ (n : ℝ) ^ 3 * Real.exp (-minCut ends w / 2)) := by sorry

end NetUnrelDesign.Main
