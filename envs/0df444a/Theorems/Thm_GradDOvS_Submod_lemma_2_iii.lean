-- Prove2me | Theorems.Thm_GradDOvS_Submod_lemma_2_iii
-- name    : GradDOvS.Submod.lemma_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:49.593542+00:00
-- url     : https://prove2.me/theorems/fffa1535-9a7a-47e1-9897-5fb4328f1f9b
-- title:
--   Lemma 2(iii), p. 17 — the Lovász extension of a submodular function is convex on [0,1]^d
-- statement:
--   Let $f : \{0,1\}^d \to \mathbb R$ be submodular: $f(A \cap B) + f(A\cup B) \le f(A) + f(B)$ for all $A, B$. Then its Lovász extension $\tilde f$ of (2) is convex on the box:
--   $$\tilde f(\lambda x + (1-\lambda) y) \le \lambda \tilde f(x) + (1-\lambda)\tilde f(y), \qquad x,y \in [0,1]^d,\ \lambda \in [0,1].$$
--
--   This is the classical theorem of Lovász (1983). It turns stochastic submodular minimization into a convex problem on $[0,1]^d$, to which (stochastic) subgradient methods apply. A version for Murota's encoding of the Lovász extension (values in $\mathbb R\cup\{+\infty\}$, normalised by $\rho(\emptyset)=0$, on all of $\mathbb R^V$) is proved on the platform as `DiscreteConvex.MConvexSetsB.lovasz_convex_iff_submodular` (Murota, Theorem 4.16); the object here is a different encoding, so that result is cited, not reused.
--
--   **Formalization Note** Of Assumptions 1–4 only submodularity (Assumption 2 on $\{0,1\}^d$) is needed and kept.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 17, Lemma 2(iii)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Lemma 2(iii), p. 17: for submodular `f`, the Lovász extension is convex on `[0,1]^d`. -/
theorem lemma_2_iii {d : ℕ} (f : Finset (Fin d) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) :
    ConvexOn ℝ (box d) (lovasz f) := by sorry

end GradDOvS.Submod
