-- Prove2me | Theorems.Thm_OAI_UniversalCoverSplitting_exists_holomorphic_local_flow
-- name    : OAI.UniversalCoverSplitting.exists_holomorphic_local_flow
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:49:54.494983+00:00
-- url     : https://prove2.me/theorems/487c3dd1-5947-4bb5-b535-79dd2b4f0128
-- title:
--   Local holomorphic flow of a holomorphic vector field, preserving commuting fields
-- statement:
--   **Setting.** $E$ is a complex Banach space, and $U \subseteq E$ is open. $V : E \to E$ and $D : E \to \mathrm{End}_{\mathbb C}(E)$ are continuous, and $V$ has complex Fréchet derivative $D(x)$ at every $x \in U$. So $V$ is a holomorphic vector field on $U$ with continuous derivative. Time is complex: a flow is a map $F : E \times \mathbb C \to E$, $(x, t) \mapsto F(x, t)$.
--
--   **Statement.** For every $p \in U$ there are an open set $O \subseteq E \times \mathbb C$ containing $(p, 0)$ and a map $F : E \times \mathbb C \to E$ such that
--   - $F$ is complex $C^1$ (hence holomorphic) on $O$ and maps $O$ into $U$;
--   - $F(x, 0) = x$ whenever $(x, 0) \in O$;
--   - $\partial_t F(q) = V(F(q))$ for every $q \in O$, i.e. $DF_q(0, 1) = V(F(q))$;
--   - $F$ carries every vector field that commutes with $V$ along: if $A : E \to E$ is continuous with complex derivative $DA(x)$ at every $x \in U$, and $DA(x)\,V(x) = D(x)\,A(x)$ for all $x \in U$ (the Lie bracket $[V, A]$ vanishes on $U$), then $DF_q(A(x), 0) = A(F(q))$ for every $q = (x, t) \in O$.
--
--   The first three items are the local existence of a holomorphic flow, with holomorphic dependence on the initial point and on complex time. This is the complex-time form of the Picard–Lindelöf theorem (Picard 1890, Lindelöf 1894). The last item is the standard fact that a flow preserves every vector field commuting with its generator. The statement uses only Mathlib. Lean: `OAI.UniversalCoverSplitting.exists_holomorphic_local_flow`. It is OpenAI's theorem `exists_holomorphicFlowData` (in `lean/OAI/Geometry/KahlerSplitting/FlowVariation.lean`), with the fields of OpenAI's structure `HolomorphicFlowData` written out as the conclusion.
-- source:
--   Picard, Mémoire sur la théorie des équations aux dérivées partielles et la méthode des approximations successives, J. Math. Pures Appl. (4) 6 (1890); Lindelöf, Sur l'application de la méthode des approximations successives aux équations différentielles ordinaires du premier ordre, C. R. Acad. Sci. Paris 118 (1894); Lean: OpenAI, Universal-cover splitting for compact Kähler manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf; Apache License 2.0), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/KahlerSplitting/FlowVariation.lean (declaration OAI.UniversalCoverSplitting.exists_holomorphicFlowData)

import Mathlib

theorem OAI.UniversalCoverSplitting.exists_holomorphic_local_flow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [CompleteSpace E] (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hV : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) :
    ∃ (O : Set (E × ℂ)) (F : E × ℂ → E), IsOpen O ∧ (p,0) ∈ O ∧
      ContDiffOn ℂ 1 F O ∧ Set.MapsTo F O U ∧
      (∀ x, (x,0) ∈ O → F (x,0) = x) ∧
      (∀ q ∈ O, fderiv ℂ F q (0,1) = V (F q)) ∧
      (∀ (A : C(E,E)) (DA : E → E →L[ℂ] E),
        (∀ x ∈ U, HasFDerivAt A (DA x) x) →
        (∀ x ∈ U, DA x (V x) = D x (A x)) →
        ∀ q ∈ O, fderiv ℂ F q (A q.1,0) = A (F q)) := by
  sorry
