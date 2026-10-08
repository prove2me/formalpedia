-- Prove2me | Theorems.Thm_KernelDRO_Duality_lemma_D_4
-- name    : KernelDRO.Duality.lemma_D_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:34.248386+00:00
-- url     : https://prove2.me/theorems/4a79b303-7583-4087-b03d-4fc5d9558d3b
-- title:
--   Lemma D.4, p. 23 — the ambiguity set $\mathcal K_{\mathcal C}$ is compact
-- statement:
--   Let $\mathcal X$ be a compact metric space with its Borel $\sigma$-algebra, $\varphi:\mathcal X\to\mathcal H$ continuous, and $\mathcal C\subseteq\mathcal H$ closed and convex. Then the ambiguity set
--   $$\mathcal K_{\mathcal C}=\Big\{P\in\mathcal P:\ \int\varphi\,dP\in\mathcal C\Big\}$$
--   is a compact subset of the space of Borel probability measures with the topology of weak convergence. It is the compact feasible set on which the primal problem attains its value.
--
--   **Formalization Note** The paper equips $\mathcal P$ with the MMD, which for a universal continuous kernel on a compact space induces the weak topology; the statement uses the weak topology and assumes only that $\varphi$ is continuous.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, §D.2, Lemma D.4, p. 23

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **Lemma D.4** (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization,
arXiv:2006.06981v3, Lemma D.4, p. 23). If `𝒳` is compact, under Assumption 3.1 (`𝒞` closed and
convex), the ambiguity set `𝒦_𝒞 = {P ∈ 𝒫 : ∫ φ dP ∈ 𝒞}` is compact.

**Formalization Note.** Compactness is in the topology of `ProbabilityMeasure X`, the topology of
weak convergence. The paper equips `𝒫` with MMD, which induces the same topology for a universal
continuous kernel on a compact `𝒳`; the proof's "bijective isometry" needs such a kernel, while the
statement here assumes only that `φ` is continuous. `𝒳` is a compact metric space with its Borel
σ-algebra. Of Assumption 3.1 only the clauses on `𝒞` concern this statement. -/
theorem lemma_D_4 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : X → H) (hφ : Continuous φ) (C : Set H) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) :
    IsCompact (ambiguitySet φ C) := by sorry

end KernelDRO.Duality
