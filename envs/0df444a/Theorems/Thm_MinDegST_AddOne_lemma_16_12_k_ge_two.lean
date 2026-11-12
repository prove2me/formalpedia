-- Prove2me | Theorems.Thm_MinDegST_AddOne_lemma_16_12_k_ge_two
-- name    : MinDegST.AddOne.lemma_16_12_k_ge_two
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:17:19.264958+00:00
-- url     : https://prove2.me/theorems/ef5c157f-368e-47ae-8d49-facc99780c38
-- title:
--   Lemma 16.12 for Δ⋆ ≥ 2 (corrected: false at Δ⋆ = 1)
-- statement:
--   **Source** (p. 44, Lemma 16.12): there exist a forest $F^{\mathrm{gui}} \subseteq T^\star$ and a region $R_{\mathrm{bad}} \in \mathcal{R}$ such that every other region has an edge of $F^{\mathrm{gui}}$ leaving it and every vertex has degree $\le \Delta^\star - 1$ in $F^{\mathrm{gui}}$.
--
--   **Variant:** the same statement (threshold form $k$, $T^\star$ a spanning tree of maximum degree $\le k$, setting of §16.3) under the extra hypothesis $k \ge 2$.
--
--   **Difference:** the hypothesis $2 \le k$ is added; at $k = 1$ the source statement fails for $G = K_2$ (two singleton regions, clause 1 needs an edge, clause 2 forbids every edge). The proof's step "retained $\Delta^\star - 1 \ge 1$ edges to its children" uses it.
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 44, Lemma 16.12 (corrected)

import Mathlib
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Molecules

namespace MinDegST.AddOne

/-- **Variant of Lemma 16.12** (threshold form, with the added hypothesis `2 ≤ k`; see I1).
Setting of §16.3: `F` a
forest of the connected graph `G` of maximum degree `≤ k + 1` with `f ≥ 2` components, `M` its
`θ`-molecular decomposition for `θ = ⌈10n/f⌉`, `𝓡` the reducible regions, and `T⋆` a spanning tree
of `G` of maximum degree `≤ k` (`k = Δ⋆`, `T⋆` optimal, in the paper). Then there are a forest
`F^gui ≤ T⋆` and a region `R_bad ∈ 𝓡` such that
1. every region `R ∈ 𝓡 \ {R_bad}` has an edge `(x, y)` of `F^gui` with `x ∈ R`, `y ∉ R`;
2. every node `u` has `deg_{F^gui}(u) ≤ k − 1` (in `ℤ`). -/
theorem lemma_16_12_k_ge_two (n : ℕ) (G : SimpleGraph (Fin n)) (k : ℕ) (F : SimpleGraph (Fin n))
    (M : Finset (Molecule n)) (𝓡 : Finset (Finset (Fin n))) (Tstar : SimpleGraph (Fin n))
    (hk2 : 2 ≤ k) (hG : G.Connected) (hT : IsSpanningTree G Tstar) (hTk : ∀ v, deg Tstar v ≤ k)
    (hF : IsForestOf G F) (hfeas : Feasible k F) (hf : 2 ≤ numComponents F)
    (hM : IsThetaDecomp F k ⌈(10 * n : ℝ) / (numComponents F : ℝ)⌉₊ M)
    (h𝓡 : IsRegionsOf G F k M 𝓡) :
    ∃ Fgui : SimpleGraph (Fin n), Fgui ≤ Tstar ∧ ∃ Rbad ∈ 𝓡,
      (∀ R ∈ 𝓡, R ≠ Rbad → ∃ x y, Fgui.Adj x y ∧ x ∈ R ∧ y ∉ R) ∧
      ∀ u, (deg Fgui u : ℤ) ≤ (k : ℤ) - 1 := by sorry

end MinDegST.AddOne
