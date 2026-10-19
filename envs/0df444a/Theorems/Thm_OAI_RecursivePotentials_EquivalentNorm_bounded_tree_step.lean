-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_EquivalentNorm_bounded_tree_step
-- name    : OAI.RecursivePotentials.EquivalentNorm.bounded_tree_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:09:49.949327+00:00
-- url     : https://prove2.me/theorems/ac41cc5a-24da-42db-9059-f52c14b36f79
-- title:
--   Norm growth along a weakly null sequence under a positive asymptotic modulus
-- statement:
--   Let $E$ be a real normed space. An *equivalent norm* on $E$ is a seminorm $N$ together with constants $0<a\le b$ such that $a\|x\|\le N(x)\le b\|x\|$ for all $x\in E$. A *cofinite subspace* is a closed linear subspace $F\subseteq E$ such that $E/F$ is finite-dimensional. The (one-sided) *modulus of asymptotic uniform convexity* of $N$ is
--
--   $$\bar\delta_N(t)=\inf_{x\in E,\ N(x)=1}\ \sup_{F}\ \inf_{y\in F,\ N(y)=1}\bigl(N(x+ty)-1\bigr),$$
--
--   the supremum running over all cofinite subspaces $F$ of $E$. A sequence $(d_k)_{k\in\mathbb{N}}$ in $E$ is *weakly null* if $f(d_k)\to0$ as $k\to\infty$ for every continuous linear functional $f:E\to\mathbb{R}$.
--
--   **Theorem.** Let $(N,a,b)$ be an equivalent norm on an infinite-dimensional real normed space $E$. Let $u\in E$ with $u\neq0$, let $(d_k)_{k\in\mathbb{N}}$ be weakly null in $E$, and let $M,c,\gamma>0$ satisfy $\|u\|\le M$, $\|d_k\|\ge c$ for all $k$, and
--
--   $$\gamma<\bar\delta_N\Bigl(\frac{ac}{2bM}\Bigr).$$
--
--   Then there exists $k\in\mathbb{N}$ with
--
--   $$\Bigl(1+\frac{\gamma}{2}\Bigr)N(u)\le N(u+d_k).$$
--
--   This is the single step of a growth argument: if the modulus is positive at the indicated radius, then moving from $u$ along a suitable member of any weakly null, uniformly long sequence of increments multiplies $N(u)$ by at least $1+\gamma/2$. Iterating along branches of bounded trees produces unbounded growth, which is how the existence of AUC renormings is ruled out.
--
--   **Formalization Note** `EquivalentNorm E` bundles the seminorm `N` with the constants `lower` $=a$ and `upper` $=b$; `A.modulus t` is defined with Lean's `sInf`/`sSup` on real sets (which return $0$ on empty or unbounded sets), but on an infinite-dimensional space and for $t\ge0$ all the sets involved are nonempty and bounded, so it is the genuine inf-sup-inf above. Here `A.N u` is $N(u)$, `A.lower` $=a$, `A.upper` $=b$, and infinite dimensionality is the hypothesis `¬Module.Finite ℝ E`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean#L206-L257

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.EquivalentNorm
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology
variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

theorem OAI.RecursivePotentials.EquivalentNorm.bounded_tree_step (hE : ¬Module.Finite ℝ E) {u : E} (hu : u ≠ 0)
    (d : ℕ → E) (hd : WeaklyNull d) {M c γ : ℝ} (hM : 0 < M) (hc : 0 < c)
    (huM : ‖u‖ ≤ M) (hdc : ∀ k, c ≤ ‖d k‖) (hγ : 0 < γ)
    (hmod : γ < A.modulus (A.lower * c / (2 * A.upper * M))) :
    ∃ k, (1 + γ / 2) * A.N u ≤ A.N (u + d k) := by sorry
