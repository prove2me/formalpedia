-- Prove2me | Theorems.Thm_GradDOvS_Submod_lemma_2_i
-- name    : GradDOvS.Submod.lemma_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:56.705674+00:00
-- url     : https://prove2.me/theorems/943f2441-ab90-4bcc-93fa-dbd451643922
-- title:
--   Lemma 2(i), p. 17 — the Lovász extension agrees with f on {0,1}^d
-- statement:
--   Let $f : \{0,1\}^d \to \mathbb R$ and $\tilde f$ its Lovász extension (2). For every $A \subseteq \{1,\dots,d\}$, with indicator vector $\mathbb 1_A$,
--   $$\tilde f(\mathbb 1_A) = f(A).$$
--
--   So $\tilde f$ is an extension of $f$ from the vertices of the cube to $[0,1]^d$.
--
--   **Formalization Note** The page assumes Assumptions 1–4; none is needed, and the statement is made for every $f$.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 17, Lemma 2(i)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Lemma 2(i), p. 17: the Lovász extension agrees with `f` on `{0,1}^d`. -/
theorem lemma_2_i {d : ℕ} (f : Finset (Fin d) → ℝ) (A : Finset (Fin d)) :
    lovasz f (ind A) = f A := by sorry

end GradDOvS.Submod
