-- Prove2me | Theorems.Thm_NonsmoothNewton_Local_lemma_2_2
-- name    : NonsmoothNewton.Local.lemma_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:02:11.571188+00:00
-- url     : https://prove2.me/theorems/4a3ea490-c129-40e2-bbe7-57083ca4a6cc
-- title:
--   Lemma 2.2 — $F'(x;\cdot)$ is Lipschitz and $F'(x;h)=Vh$ for some $V\in\partial F(x)$
-- statement:
--   Let $E$, $G$ be finite-dimensional real normed spaces and $F : E \to G$ locally Lipschitz, and suppose the one-sided directional derivative $F'(x;h)$ exists for every $h \in E$. Then
--
--   1. the map $h \mapsto F'(x;h)$ is Lipschitz: there is $K \ge 0$ with $\|F'(x;h) - F'(x;h')\| \le K\|h - h'\|$ for all $h, h'$;
--   2. for every $h$ there is $V \in \partial F(x)$ with
--   $$
--   F'(x;h) = V h .
--   $$
--
--   Part (ii) says the directional derivative is realised by an element of the generalized Jacobian, direction by direction; together with (i) it is used to pass between the characterizations of semismoothness in Theorem 2.3.
--
--   **Formalization Note** The paper's $\mathbb R^n \to \mathbb R^m$ is generalised to finite-dimensional normed spaces; the Lipschitz constant is existential.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 356, Lemma 2.2

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology

namespace NonsmoothNewton.Local

/-- Qi–Sun (1993), Lemma 2.2, p. 356. If `F` is locally Lipschitz and `F'(x; h)` exists for
every `h`, then (i) `h ↦ F'(x; h)` is Lipschitz and (ii) for every `h` there is
`V ∈ ∂F(x)` with `F'(x; h) = V h`. -/
theorem lemma_2_2 {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (F : E → G) (hF : LocallyLipschitz F) (x : E)
    (hdir : ∀ h : E, ∃ d : G, HasDirDerivAt F x h d) :
    (∃ K : NNReal, LipschitzWith K (fun h : E => dirDeriv F x h)) ∧
    ∀ h : E, ∃ V ∈ NonsmoothNewton.Shared.clarkeJac F x, dirDeriv F x h = V h := by sorry

end NonsmoothNewton.Local
