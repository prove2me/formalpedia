-- Prove2me | Theorems.Thm_OAI_IndependentProducts_weaklyNull_approx_cofinite
-- name    : OAI.IndependentProducts.weaklyNull_approx_cofinite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T02:49:15.688847+00:00
-- url     : https://prove2.me/theorems/09a55b91-5753-4594-a118-6a3e842c444d
-- title:
--   Weakly null sequences approach every closed finite-codimensional subspace
-- statement:
--   Let $X$ be a real normed space. A sequence $(u_n)_{n\in\mathbb{N}}$ in $X$ is *weakly null* if $f(u_n)\to0$ as $n\to\infty$ for every continuous linear functional $f:X\to\mathbb{R}$. Let $F\subseteq X$ be a linear subspace that is closed and has finite codimension, meaning that the quotient space $X/F$ is finite-dimensional.
--
--   If $(u_n)$ is weakly null, then the $u_n$ are eventually arbitrarily close to $F$: for every $\varepsilon>0$,
--
--   $$\exists\,n_0\ \ \forall n\ge n_0\ \ \exists z\in F:\qquad \|u_n-z\|<\varepsilon .$$
--
--   Equivalently, $\operatorname{dist}(u_n,F)\to0$.
--
--   This links weak nullity with the asymptotic moduli of a normed space, which are defined through closed finite-codimensional subspaces: a weakly null sequence of increments can be replaced, up to an arbitrarily small error in norm, by vectors lying in any prescribed subspace of this kind. It is the approximation step in the proof that a tree with weakly null branch increments obstructs asymptotically uniformly convex renormings.
--
--   **Formalization Note** Completeness of $X$ is not assumed. Weak nullity is `WeaklyNull u`, stated directly against continuous real-linear functionals; membership of $F$ in `CofiniteSubspaces X` means that $F$ is closed and the quotient $X/F$ is finite-dimensional. The conclusion is phrased with the filter `atTop`, i.e. eventually in $n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ProductSpaces/TreeObstruction.lean#L35-L56

import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction

open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uX
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.IndependentProducts.weaklyNull_approx_cofinite {u : ℕ → X} (hu : WeaklyNull u)
    (F : Submodule ℝ X) (hF : F ∈ CofiniteSubspaces X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ z ∈ F, ‖u n - z‖ < ε := by sorry
