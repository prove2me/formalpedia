-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_22
-- name    : MixedCloning.Optimal.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:59.737289+00:00
-- url     : https://prove2.me/theorems/fcfaa8bc-64f3-4aba-8bf9-5ccfbc23d11d
-- title:
--   Lemma 22 — projector-integral recursion through Lift
-- statement:
--   Let $d\ge1$, $1\le r\le d$, and let $\lambda,\mu$ have height at most $d$. Suppose $\lambda'\preceq\lambda$ and $\ell(\lambda')\le r-1$. For any isometric branching intertwiner families,
--
--   $$S^{(d,r)}_{\lambda\mu}=\frac{s_\lambda(1^r)}{s_{\lambda'}(1^{r-1})}\sum_{\mu'\preceq\mu}\operatorname{Lift}^{\lambda\mu}_{\lambda'\mu'}\bigl(S^{(d-1,r-1)}_{\lambda'\mu'}\bigr).$$
--
--   The formula includes $r=1$: rank-zero projectors in the smaller dimension are defined, and the only possible $\lambda'$ is empty. This supplies the integral term of the simultaneous dimension-and-rank recursion.
--
--   Differences from the source:
--   - generalization: Gelfand–Tsetlin embeddings → every isometric U(d−1) intertwining family; reason: multiplicity-free branching makes each component unique up to a phase which cancels in Lift
--   - encoding: dimension d ≥ 1 → dimension d+1 with d ≥ 0; reason: successor indexing avoids truncated subtraction
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders, counts and contents
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 23, Lemma 22

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_22 (d r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d+1)
    (L M : YoungDiagram) (hL : height L ≤ d+1) (hM : height M ≤ d+1)
    (E : BranchFamily d L) (G : BranchFamily d M)
    (hE : IsBranchFamily d L E) (hG : IsBranchFamily d M G)
    (L' : {L' : YoungDiagram // L' ∈ branches d L}) (hL'r : height L'.val ≤ r-1) :
    schurIntegral r L M (schurBasis L (d+1)) (schurBasis M (d+1)) =
      ((schurCount L r : ℂ) / schurCount L'.val (r-1)) •
        ∑ M' : {M' : YoungDiagram // M' ∈ branches d M},
          lift E G L' M' (schurIntegral (r-1) L'.val M'.val
            (schurBasis L'.val d) (schurBasis M'.val d)) := by sorry

end MixedCloning.Optimal
