-- Prove2me | Theorems.Thm_GradDOvS_Submod_lemma_2_iv
-- name    : GradDOvS.Submod.lemma_2_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:47.778906+00:00
-- url     : https://prove2.me/theorems/bdac1759-af4d-41be-a4d0-87bc15d72d48
-- title:
--   Lemma 2(iv), p. 17, eq. (3) — the chain differences form a subgradient of the Lovász extension
-- statement:
--   Let $f : \{0,1\}^d \to \mathbb R$ be submodular, $x \in [0,1]^d$, and $\alpha$ any consistent permutation of $x$ ($x_{\alpha(1)} \ge \dots \ge x_{\alpha(d)}$), with neighbouring points $S^{x,i} = \{\alpha(1),\dots,\alpha(i)\}$. Define $g \in \mathbb R^d$ by (3):
--   $$g_{\alpha(i)} = f(S^{x,i}) - f(S^{x,i-1}), \qquad i = 1,\dots,d.$$
--   Then $g$ is a subgradient of $\tilde f$ at $x$ relative to the box:
--   $$\langle g, x - y\rangle \ge \tilde f(x) - \tilde f(y) \qquad \text{for all } y \in [0,1]^d.$$
--
--   This explicit subgradient, computable from $d+1$ function values, is what the stochastic estimator (4) estimates.
--
--   **Formalization Note** The statement holds for every consistent permutation of $x$, not only the canonical one used to evaluate $\tilde f$. Of Assumptions 1–4 only submodularity is needed and kept.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 17, Lemma 2(iv), eq. (3); subdifferential defined on p. 17

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Lemma 2(iv), p. 17, eq. (3): for submodular `f`, `x ∈ [0,1]^d` and any consistent permutation
`α` of `x`, the vector `g_{α(i)} = f(S^{x,i}) - f(S^{x,i-1})` is a subgradient of the Lovász
extension at `x` relative to `[0,1]^d`. -/
theorem lemma_2_iv {d : ℕ} (f : Finset (Fin d) → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (x : Fin d → ℝ) (hx : x ∈ box d) (α : Equiv.Perm (Fin d)) (hα : IsConsistentPerm x α) :
    IsSubgradOn f x (chainGrad f α) := by sorry

end GradDOvS.Submod
