-- Prove2me | Theorems.Thm_GarrettFA_range_weakDual_coeFn_of_isInitTopology
-- name    : GarrettFA.range_weakDual_coeFn_of_isInitTopology
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:42:53.850026+00:00
-- url     : https://prove2.me/theorems/a73437e2-8919-4c3f-9afb-09fe8a51438b
-- title:
--   Claim 5.0.7 — the weak dual of $V_{\mathrm{init}}$ is the whole limit
-- statement:
--   Let $V$ be a vector space over $\mathbb K=\mathbb R$ or $\mathbb C$ whose (Hausdorff) topology is the topology of $V_{\rm init}$. Then the image of its weak dual under $\lambda\mapsto(\lambda(v))_{v\in V}$ is exactly the set of all linear functionals:
--
--   $$\{\,(\lambda(v))_{v\in V} : \lambda\in V_{\rm init}^*\,\} = \{\, g:V\to\mathbb K \ :\ g \text{ linear}\,\}.$$
--
--   **Formalization Note** With the identification described for Claim 5.0.6, $\lim_\Phi V^*_\Phi$ is the space of all linear functionals on $V$ inside $\mathbb K^V$, so "the weak dual of $V_{\rm init}$ is the limit" becomes the equality of images above.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 9, Claim 5.0.7

import Definitions.Def_GarrettFA_IsInitTopology

namespace GarrettFA
theorem range_weakDual_coeFn_of_isInitTopology {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    (hV : IsInitTopology 𝕜 V) :
    Set.range (fun f : WeakDual 𝕜 V => (f : V → 𝕜)) = {g : V → 𝕜 | IsLinearMap 𝕜 g} := by sorry
end GarrettFA
