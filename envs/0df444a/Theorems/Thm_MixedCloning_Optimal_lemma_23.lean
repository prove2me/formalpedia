-- Prove2me | Theorems.Thm_MixedCloning_Optimal_lemma_23
-- name    : MixedCloning.Optimal.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:07.996254+00:00
-- url     : https://prove2.me/theorems/da794879-00f3-4102-a07f-fc027c0a2ce3
-- title:
--   Lemma 23 — Schur ratio identities under first-row deletion
-- statement:
--   Let $1\le r\le d$, let $\lambda,\mu$ have height at most $r$, and assume $\lambda_1\ge\mu_1$. Write $\lambda^-$ and $\mu^-$ for deletion of the first row. Then both identities hold:
--
--   $$\frac{s_\lambda(1^r)}{s_\lambda(1^d)}\frac{s_{\lambda^-}(1^{d-1})}{s_{\lambda^-}(1^{r-1})}=\frac{s_{\lambda\cup\mu}(1^r)}{s_{\lambda\cup\mu}(1^d)}\frac{s_{\lambda^-\cup\mu^-}(1^{d-1})}{s_{\lambda^-\cup\mu^-}(1^{r-1})},$$
--
--   $$\frac{s_{\lambda\cup\mu}(1^r)}{s_{\lambda\cup\mu}(1^d)}\frac{s_\lambda(1^d)}{s_{\lambda^-}(1^{d-1})}=\frac{s_{\lambda^-\cup\mu^-}(1^{r-1})}{s_{\lambda^-\cup\mu^-}(1^{d-1})}\frac{s_\lambda(1^r)}{s_{\lambda^-}(1^{r-1})}.$$
--
--   The height assumptions ensure all denominators are positive, including $r=1$, where the deleted diagrams are empty. These are the scalar coefficient identities used in the defect recursion.
--
--   Differences from the source:
--   - encoding: partitions and tableaux with symbols starting at 1 → YoungDiagram cells and Fin alphabets starting at 0; reason: shifting indices preserves all shapes, orders, counts and contents
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), p. 25, Lemma 23, both displays

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lemma_23 (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) (hrd : r ≤ d)
    (L M : YoungDiagram) (hL : height L ≤ r) (hM : height M ≤ r)
    (hfirst : M.rowLen 0 ≤ L.rowLen 0) :
    ratio L r d * ((schurCount (tailDiagram L) (d-1) : ℝ) / schurCount (tailDiagram L) (r-1)) =
      ratio (L ⊔ M) r d * ((schurCount (tailDiagram L ⊔ tailDiagram M) (d-1) : ℝ) /
        schurCount (tailDiagram L ⊔ tailDiagram M) (r-1)) ∧
    ratio (L ⊔ M) r d * ((schurCount L d : ℝ) / schurCount (tailDiagram L) (d-1)) =
      ratio (tailDiagram L ⊔ tailDiagram M) (r-1) (d-1) *
        ((schurCount L r : ℝ) / schurCount (tailDiagram L) (r-1)) := by sorry

end MixedCloning.Optimal
