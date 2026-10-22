-- Prove2me | Theorems.Thm_GradDOvS_Submod_lemma_2_ii
-- name    : GradDOvS.Submod.lemma_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:54.675349+00:00
-- url     : https://prove2.me/theorems/fc0934c7-dcd0-46ee-bf14-99b1d78d67e6
-- title:
--   Lemma 2(ii), p. 17 (corrected: equal minima) — min of the Lovász extension over [0,1]^d equals min f
-- statement:
--   Let $f : \{0,1\}^d \to \mathbb R$ and $\tilde f$ its Lovász extension. Then
--   1. $\tilde f(x) \ge \min_{A} f(A)$ for every $x \in [0,1]^d$, so (with Lemma 2(i)) $\displaystyle\min_{x\in[0,1]^d} \tilde f(x) = \min_{A \subseteq\{1,\dots,d\}} f(A)$;
--   2. for every $A$: $\mathbb 1_A$ minimizes $\tilde f$ over $[0,1]^d$ if and only if $A$ minimizes $f$.
--
--   Hence the relaxed problem (5) and problem (1) have the same optimal value, and their minimizers agree on $\{0,1\}^d$.
--
--   **Formalization Note** The page states $\arg\min_{[0,1]^d} \tilde f = \arg\min_{\{0,1\}^d} f$ as sets, which is false: for $d = 1$ and $f \equiv 0$ the left side is $[0,1]$ and the right side $\{0,1\}$. The statement formalized is the corrected one above, which is what the page uses ("the original problem (1) is equivalent to the relaxed problem (5)", p. 18). No submodularity is needed, so it is stated for every $f$.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 17, Lemma 2(ii) (corrected; see Formalization Note)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Lemma 2(ii), p. 17, corrected (the printed equality of argmin sets fails for constant `f`):
the minimum of the Lovász extension over `[0,1]^d` equals `min f`, and a point of `{0,1}^d`
minimizes the Lovász extension over `[0,1]^d` iff it minimizes `f`. -/
theorem lemma_2_ii {d : ℕ} (f : Finset (Fin d) → ℝ) :
    (∀ x ∈ box d, minf f ≤ lovasz f x) ∧
      ∀ A : Finset (Fin d), ((∀ x ∈ box d, lovasz f (ind A) ≤ lovasz f x) ↔ f A = minf f)
    := by sorry

end GradDOvS.Submod
