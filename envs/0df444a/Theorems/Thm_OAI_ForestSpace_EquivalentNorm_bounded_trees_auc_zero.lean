-- Prove2me | Theorems.Thm_OAI_ForestSpace_EquivalentNorm_bounded_trees_auc_zero
-- name    : OAI.ForestSpace.EquivalentNorm.bounded_trees_auc_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:24:46.075607+00:00
-- url     : https://prove2.me/theorems/27d75fef-61ff-4dc8-a07d-16a9f0d51ad3
-- title:
--   Bounded weakly null trees force the AUC modulus of an equivalent norm to vanish at $t=\alpha/(2\beta)$
-- statement:
--   Let $E$ be an infinite-dimensional real normed space with norm $\|\cdot\|$, and let $N$ be an equivalent norm on $E$ with constants $0<\alpha\le\beta$, that is, $\alpha\|z\|\le N(z)\le\beta\|z\|$ for all $z\in E$. Let $\operatorname{cof}(E)$ be the family of closed linear subspaces of $E$ of finite codimension. For $t\in\mathbb{R}$ the asymptotic uniform convexity modulus of $N$ is
--
--   $$
--   \delta_N(t)=\inf_{N(x)=1}\ \sup_{F\in\operatorname{cof}(E)}\ \inf_{\substack{y\in F\\ N(y)=1}}\big(N(x+ty)-1\big),
--   $$
--
--   and $N$ is asymptotically uniformly convex (AUC) if $\delta_N(t)>0$ for every $t>0$.
--
--   Suppose that for every height $h\ge1$ there is a tree $(u_h(s))_s$ in $E$, indexed by finite sequences $s$ of natural numbers (write $|s|$ for the length and $s^\frown j$ for $s$ extended by $j$), such that for all $h\ge1$:
--
--   1. $\|u_h(s)\|=1$ whenever $|s|\le h$;
--   2. $\|u_h(s^\frown j)-u_h(s)\|\ge1$ whenever $|s|<h$ and $j\in\mathbb{N}$;
--   3. whenever $|s|<h$, the increments are weakly null: $\varphi\big(u_h(s^\frown j)-u_h(s)\big)\to0$ as $j\to\infty$ for every continuous linear functional $\varphi$ on $E$.
--
--   Then
--
--   $$
--   \delta_N\Big(\frac{\alpha}{2\beta}\Big)=0 .
--   $$
--
--   In particular $N$ is not AUC. Conditions 1–3 involve only the original norm and the weak topology, so one such family of trees rules out AUC for every equivalent norm at once; the main theorem uses this with the trees of path functionals in the finite-height forest to show that $J(T)^*$ has no equivalent AUC norm.
--
--   **Formalization Note** The equivalent norm is a structure `EquivalentNorm E α β` holding a seminorm `N` together with `0 < α`, `α ≤ β` and `α*‖x‖ ≤ N x ≤ β*‖x‖`. The trees are a single function `u : ℕ → List ℕ → E` whose children are `s ++ [j]`; values at height `0` or at lists longer than `h` are unconstrained. `WeakNull d` means `φ (d n) → 0` for every `φ : StrongDual ℝ E`, and `aucModulus E R.N t` is the inf–sup–inf above, built with `sInf`/`sSup` on sets of reals over `Cofinite E`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Renorming.lean#L256-L303

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α β : ℝ} (R : EquivalentNorm E α β)

theorem OAI.ForestSpace.EquivalentNorm.bounded_trees_auc_zero (hI : ¬FiniteDimensional ℝ E)
    (u : ℕ → List ℕ → E)
    (hu : ∀ h ≥ 1, ∀ s : List ℕ, s.length ≤ h → ‖u h s‖ = 1)
    (hd : ∀ h ≥ 1, ∀ s : List ℕ, s.length < h → ∀ j,
      1 ≤ ‖u h (s++[j])-u h s‖)
    (hweak : ∀ h ≥ 1, ∀ s : List ℕ, s.length < h →
      WeakNull (fun j => u h (s++[j])-u h s)) :
    aucModulus E R.N (α/(2*β)) = 0 := by sorry
