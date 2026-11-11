-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_finite_reindexing
-- name    : MultiwayGap2325.Main.finite_reindexing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:06:07.304205+00:00
-- url     : https://prove2.me/theorems/8c66c416-b61f-415e-8a34-aed7123093f4
-- title:
--   §1 — finite vertex reindexing preserves both objectives
-- statement:
--   Let $V$ be any finite vertex type, let $I$ be an instance on $V$, and let $e:V\simeq\{0,\ldots,|V|-1\}$ be the equivalence chosen by `Fintype.equivFin V`. Let $J$ be the graph obtained by transporting its edges, weights and terminals along $e$. Transport of a labeling or embedding preserves feasibility and its objective value. Consequently,
--   $$
--   \operatorname{OPT}(J)=\operatorname{OPT}(I),\qquad
--   \operatorname{LP}(J)=\operatorname{LP}(I),\qquad
--   \operatorname{gap}(J)=\operatorname{gap}(I).
--   $$
--   Thus a supremum over the vertex sets $\operatorname{Fin}(n)$ includes every finite graph up to reindexing. This is an encoding obligation for the source's finite-instance quantifier.
--
--   Differences from the source:
--   - encoding: an arbitrary finite undirected graph with distinct terminals → a graph on Fin n with Fin k terminals and an ordered edge list; reason: all finite vertex types admit reindexing; opposite orientations aggregate and loops have zero cost; neither n nor real weights are bounded
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), §1, pp. 1–2, equations (1),(2) and definition of G_k

import Definitions.Def_MultiwayGap2325_Main_FiniteGap

namespace MultiwayGap2325.Main

/-- Every finite vertex type is represented in the Fin-n supremum of §1, pp.1–2. -/
theorem finite_reindexing {V : Type*} [Fintype V] {k : ℕ}
    (I : MultiwayCut.Instance V k) :
    let e := Fintype.equivFin V
    let J := reindex I e
    (∀ c : V → Fin k,
      MultiwayCut.IsFeasibleLabeling J (c ∘ e.symm) ↔
        MultiwayCut.IsFeasibleLabeling I c) ∧
    (∀ x : V → Fin k → ℝ,
      MultiwayCut.IsFeasibleEmbedding J (x ∘ e.symm) ↔
        MultiwayCut.IsFeasibleEmbedding I x) ∧
    (∀ c : V → Fin k,
      MultiwayCut.cutWeight J (c ∘ e.symm) = MultiwayCut.cutWeight I c) ∧
    (∀ x : V → Fin k → ℝ,
      MultiwayCut.relaxValue J (x ∘ e.symm) = MultiwayCut.relaxValue I x) ∧
    integralOpt J = integralOpt I ∧ fractionalOpt J = fractionalOpt I ∧
      instanceGap J = instanceGap I := by sorry

end MultiwayGap2325.Main
