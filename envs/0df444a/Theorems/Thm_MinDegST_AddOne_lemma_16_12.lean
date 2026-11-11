-- Prove2me | Theorems.Thm_MinDegST_AddOne_lemma_16_12
-- name    : MinDegST.AddOne.lemma_16_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:05.88901+00:00
-- url     : https://prove2.me/theorems/73a63c71-f22c-4f38-b424-3fcd27219c62
-- title:
--   Lemma 16.12 — a guiding forest inside an optimal spanning tree (stated as printed; false at Δ⋆ = 1, see insight I1)
-- statement:
--   In the setting of §16.3 — $G$ connected on $n$ nodes, $F$ a forest of $G$ of maximum degree at most $k+1$ with $f\ge2$ components, $M$ a $\theta$-molecular decomposition of $F$ for $\theta=\lceil 10n/f\rceil$, $\mathcal R$ its reducible regions, and $T^\star$ a spanning tree of $G$ of maximum degree at most $k$ — there exist a forest $F^{gui}\le T^\star$ and a region $R_{bad}\in\mathcal R$ such that
--   $$\forall R\in\mathcal R\setminus\{R_{bad}\}\ \exists (x,y)\in F^{gui}:\ x\in R,\ y\notin R,\qquad\text{and}\qquad \forall u:\ \deg_{F^{gui}}(u)\le k-1 .$$
--   In the paper $k=\Delta^\star$ and $T^\star$ is an optimal spanning tree. The guiding forest supplies the exit edges of the leader mapping that proves the flow lower bound (Lemma 16.9).
--
--   The statement is false when $k=\Delta^\star=1$ (insight I1: $G=K_2$, $F$ edgeless, two singleton regions); it is stated as printed.
--
--   Differences from the source:
--   - generalization: T⋆ an optimal spanning tree (maximum degree Δ⋆), F feasible w.r.t. Δ⋆, bound Δ⋆ − 1 → any threshold k and any spanning tree T⋆ of maximum degree ≤ k, F of maximum degree ≤ k + 1, regions w.r.t. k, bound k − 1; reason: the proof uses only that T⋆ has maximum degree ≤ k; k = Δ⋆ with an optimal T⋆ is the source's case
--   - reading: R is the set of reducible regions of 'the' molecular decomposition (no hypotheses printed) → hypotheses of §16.3: f ≥ 2 components, M a θ-molecular decomposition with θ = ⌈10n/f⌉, 𝓡 its regions; reason: the lemma sits in the proof of Lemma 16.9 and uses that setting; R_bad ∈ R needs at least one region
--   - reading: for every vertex u ∈ V(F^gui), deg_{F^gui}(u) ≤ ∆⋆ − 1 → for every node u of G, (deg_{F^gui}(u) : ℤ) ≤ k − 1; reason: the proof calls F^gui a spanning subforest; the subtraction is integer subtraction, not truncated
--   - reading: Definition 14.2 introduces θ in [1,n], but §16 sets θ = ⌈10n/f⌉ → the four decomposition clauses at θ = ⌈10n/f⌉ without imposing θ ≤ n; reason: the prescribed θ exceeds n when f < 10; the same clauses still apply and cover those source instances
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 44, Lemma 16.12

import Mathlib
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Molecules

namespace MinDegST.AddOne

/-- **Lemma 16.12** (threshold form; stated as printed, see finding I1). Setting of §16.3: `F` a
forest of the connected graph `G` of maximum degree `≤ k + 1` with `f ≥ 2` components, `M` its
`θ`-molecular decomposition for `θ = ⌈10n/f⌉`, `𝓡` the reducible regions, and `T⋆` a spanning tree
of `G` of maximum degree `≤ k` (`k = Δ⋆`, `T⋆` optimal, in the paper). Then there are a forest
`F^gui ≤ T⋆` and a region `R_bad ∈ 𝓡` such that
1. every region `R ∈ 𝓡 \ {R_bad}` has an edge `(x, y)` of `F^gui` with `x ∈ R`, `y ∉ R`;
2. every node `u` has `deg_{F^gui}(u) ≤ k − 1` (in `ℤ`). -/
theorem lemma_16_12 (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (F : SimpleGraph (Fin n))
    (M : Finset (Molecule n)) (𝓡 : Finset (Finset (Fin n))) (Tstar : SimpleGraph (Fin n))
    (hG : G.Connected) (hT : IsSpanningTree G Tstar) (hTk : ∀ v, deg Tstar v ≤ k)
    (hF : IsForestOf G F) (hfeas : Feasible k F) (hf : 2 ≤ numComponents F)
    (hM : IsThetaDecomp F k ⌈(10 * n : ℝ) / (numComponents F : ℝ)⌉₊ M)
    (h𝓡 : IsRegionsOf G F k M 𝓡) :
    ∃ Fgui : SimpleGraph (Fin n), Fgui ≤ Tstar ∧ ∃ Rbad ∈ 𝓡,
      (∀ R ∈ 𝓡, R ≠ Rbad → ∃ x y, Fgui.Adj x y ∧ x ∈ R ∧ y ∉ R) ∧
      ∀ u, (deg Fgui u : ℤ) ≤ (k : ℤ) - 1 := by sorry

end MinDegST.AddOne
