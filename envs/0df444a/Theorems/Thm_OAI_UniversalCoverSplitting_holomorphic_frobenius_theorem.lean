-- Prove2me | Theorems.Thm_OAI_UniversalCoverSplitting_holomorphic_frobenius_theorem
-- name    : OAI.UniversalCoverSplitting.holomorphic_frobenius_theorem
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:49:54.275187+00:00
-- url     : https://prove2.me/theorems/5d05d05a-2701-40ba-804f-f3291a991d10
-- title:
--   Holomorphic Frobenius theorem for a field of projections
-- statement:
--   **Setting.** $E$ is a finite-dimensional complex normed space, $U \subseteq E$ is open, and $P : E \to \mathrm{End}_{\mathbb C}(E)$ is a field of continuous complex-linear maps that is complex differentiable on $U$ and idempotent there: $P_x P_x = P_x$ for $x \in U$. A vector field $V$ on an open set $O$ is *tangent to $P$* if $P_x V(x) = V(x)$ for all $x \in O$, so it takes values in the distribution $x \mapsto \operatorname{im} P_x$. The field $P$ is *involutive* on $U$ if, for every open $O \subseteq U$ and all vector fields $V, W$ that are complex differentiable on $O$ and tangent to $P$, the Lie bracket $[V, W]$ (`VectorField.lieBracket ℂ V W`) is again tangent to $P$ on $O$.
--
--   **Statement.** Let $P$ be involutive on $U$, let $p \in U$, and let $r$ and $s$ be the dimensions of the range and of the kernel of $P_p$. Then there is a partial homeomorphism $e$ from an open subset of $\mathbb C^r \times \mathbb C^s$ onto an open subset of $E$ such that
--   - $0$ is in the source of $e$, $e(0) = p$, and the target of $e$ lies in $U$;
--   - $e$ is complex $C^1$ (hence holomorphic) on its source, and $e^{-1}$ is complex $C^1$ on its target;
--   - for every $y$ in the target and every $v \in E$: $P_y v = v$ exactly when the $\mathbb C^s$-component of $D(e^{-1})_y\,v$ is $0$.
--
--   So, in the holomorphic chart $e^{-1}$, the distribution $\operatorname{im} P$ is the horizontal distribution $\mathbb C^r \times \{0\}$, and its leaves are the slices $e(\mathbb C^r \times \{c\})$.
--
--   This is the local Frobenius integrability theorem (Frobenius 1877) in the holomorphic category, with the distribution given as the image of a holomorphic field of projections. Involutivity is the hypothesis written out in full, with no auxiliary definition, so the statement uses only Mathlib. Lean: `OAI.UniversalCoverSplitting.holomorphic_frobenius_theorem`. It is OpenAI's theorem `holomorphic_frobenius` (in `lean/OAI/Geometry/KahlerSplitting/ProductCharts.lean`) with OpenAI's predicate `InvolutiveProjectionOn` unfolded into the hypothesis. OpenAI uses it to build the local product charts of a holomorphic splitting of the tangent bundle.
-- source:
--   Frobenius, Über das Pfaffsche Problem, J. reine angew. Math. 82 (1877); Lean: OpenAI, Universal-cover splitting for compact Kähler manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Universal-cover-splitting-for-compact-Kahler-manifolds-September-23-2026/paper.pdf; Apache License 2.0), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/KahlerSplitting/ProductCharts.lean (declaration OAI.UniversalCoverSplitting.holomorphic_frobenius)

import Mathlib

theorem OAI.UniversalCoverSplitting.holomorphic_frobenius_theorem {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    (hInt : ∀ O : Set E, IsOpen O → O ⊆ U → ∀ V W : E → E,
      DifferentiableOn ℂ V O → DifferentiableOn ℂ W O →
      (∀ x ∈ O, P x (V x) = V x) → (∀ x ∈ O, P x (W x) = W x) →
      ∀ x ∈ O, P x (VectorField.lieBracket ℂ V W x) = VectorField.lieBracket ℂ V W x)
    {p : E} (hp : p ∈ U) {r s : ℕ}
    (hr : Module.finrank ℂ (LinearMap.range (P p).toLinearMap) = r)
    (hs : Module.finrank ℂ (LinearMap.ker (P p).toLinearMap) = s) :
    ∃ e : OpenPartialHomeomorph ((Fin r → ℂ) × (Fin s → ℂ)) E,
      (0 : (Fin r → ℂ) × (Fin s → ℂ)) ∈ e.source ∧ e 0 = p ∧ e.target ⊆ U ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.target, ∀ v, P y v = v ↔ (fderiv ℂ e.symm y v).2 = 0 := by
  sorry
