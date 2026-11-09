-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_21
-- name    : MixedCloning.Optimal.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:07.050193+00:00
-- url     : https://prove2.me/theorems/87113018-5b3a-4310-8958-9f10c18e43d0
-- title:
--   Lemma 21 — identity recursion through Lift
-- statement:
--   Let $d\ge1$, let $\lambda,\mu$ have height at most $d$, and let $\lambda'\preceq\lambda$ have height at most $d-1$. Choose any isometric branching intertwiner families for $\lambda$ and $\mu$. The Haar-averaged embedding operation obeys
--
--   $$\sum_{\mu'\preceq\mu}\operatorname{Lift}^{\lambda\mu}_{\lambda'\mu'}(I_{\lambda'}\otimes I_{\mu'})=\frac{s_{\lambda'}(1^{d-1})}{s_\lambda(1^d)}I_\lambda\otimes I_\mu.$$
--
--   All interlacing diagrams of height at most $d-1$ are included. This is the identity term in the recursion for the separability defect.
--
--   Differences from the source:
--   - generalization: Gelfand–Tsetlin embeddings → every isometric U(d−1) intertwining family; reason: multiplicity-free branching makes each component unique up to a phase which cancels in Lift
--   - encoding: dimension d ≥ 1 → dimension d+1 with d ≥ 0; reason: successor indexing avoids truncated subtraction
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders, counts and contents
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 23, Lemma 21

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_21 (d : ℕ) (L M : YoungDiagram)
    (hL : height L ≤ d+1) (hM : height M ≤ d+1)
    (E : BranchFamily d L) (G : BranchFamily d M)
    (hE : IsBranchFamily d L E) (hG : IsBranchFamily d M G)
    (L' : {L' : YoungDiagram // L' ∈ branches d L}) :
    (∑ M' : {M' : YoungDiagram // M' ∈ branches d M}, lift E G L' M' 1) =
      ((schurCount L'.val d : ℂ) / schurCount L (d+1)) • 1 := by sorry

end MixedCloning.Optimal
