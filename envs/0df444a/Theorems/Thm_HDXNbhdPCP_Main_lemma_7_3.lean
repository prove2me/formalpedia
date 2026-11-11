-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_lemma_7_3
-- name    : HDXNbhdPCP.Main.lemma_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:58:46.060616+00:00
-- url     : https://prove2.me/theorems/531767f6-5451-48ed-98f3-4f2300c03f06
-- title:
--   Lemma 7.3 — constraint sampling
-- statement:
--   Let $X$ be a weighted 4-partite complex such that the bipartite graph $X[1,\{2,3\}]$ is a $K_0q^{-1/2}$-expander and the middle edge $(x_2,x_3)$ of a random facet is uniform on $E=X[2,3]$ (both hold for the complex of §7.2, by Theorem 6.1 and by the coset symmetry noted on p. 49). Let $\mu_L$ be the law of $x_1$ and $Q_s$ the law of $(x_2,x_3)$ given $x_1=s$. Then there is a constant $K_1$, depending only on $K_0$, such that for every $F\subseteq E$ of density $p=|F|/|E|>0$,
--   $$\Pr_{s\sim\mu_L}\Big[Q_s(F)<\frac p2\Big]\le\frac{K_1}{qp}.$$
--
--   In the soundness analysis of the Label Cover instance (Lemma 7.4) it shows that few left vertices see the violated host edges at less than half their density.
--
--   Differences from the source:
--   - generalization: the specific complex X of §7.2 (Theorem 6.1 with the parameters (7.1), prime q) → every weighted 4-partite X and every q > 0 such that X[1, {2, 3}] is a K₀ q^{-1/2}-expander and the middle edge is uniform on E; O(1) = K₁ depending on K₀ only; reason: the proof uses exactly these two properties (Theorem 6.1 item 2 and p. 49); the §7.2 complex has both
--   - encoding: colours 1, 2, 3, 4; μ_L, Q_s → Fin 4 colours 0, …, 3; μ_L = law of x₀, Q_s = law of (x₁, x₂) given x₀ = s; reason: Lean convention; same quantities
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 49, Lemma 7.3 (setting of §7.2, pp. 47-49)

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex

namespace HDXNbhdPCP.Main

/-- Lemma 7.3 (constraint sampling), for every 4-partite complex `X` (colours `0, 1, 2, 3` for the
paper's `1, 2, 3, 4`) whose graph `X[1, {2, 3}]` is a `K₀ q^{-1/2}`-expander (Theorem 6.1, item 2)
and whose middle edge `(x₂, x₃)` is uniform on `E = X[2, 3]` (p. 49). `μ_L` is the law of `x₁`
and `Q_s` the law of the middle edge given `x₁ = s`. -/
theorem lemma_7_3 :
    ∀ K₀ : ℝ, 0 < K₀ → ∃ K₁ : ℝ, 0 < K₁ ∧
    ∀ q : ℝ, 0 < q →
    ∀ (V : Fin 4 → Type) (X : ColoredComplex (Fin 4) V), FinDist.IsProb X →
      (X.setPairGraph {0} {1, 2}).IsExpander (K₀ * q ^ (-(1 / 2 : ℝ))) →
      FinDist.Same (X.pairGraph 1 2) (FinDist.uniform (X.pairGraph 1 2).supp) →
      ∀ F : Finset (V 1 × V 2), F ⊆ (X.pairGraph 1 2).supp → 0 < F.card →
        (FinDist.map X (fun x => x 0)).prob (fun s =>
            (FinDist.cond X (fun x => x 0 = s)).prob (fun x => (x 1, x 2) ∈ F) <
              ((F.card : ℝ) / (X.pairGraph 1 2).supp.card) / 2) ≤
          K₁ / (q * ((F.card : ℝ) / (X.pairGraph 1 2).supp.card)) := by sorry

end HDXNbhdPCP.Main
