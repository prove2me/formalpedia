-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_ramsey_congruent_iff
-- name    : OAI.EuclideanRamsey.ramsey_congruent_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:35:42.835028+00:00
-- url     : https://prove2.me/theorems/cf83ca03-3df7-4727-a4dc-9fc4b13ea455
-- title:
--   Being Ramsey is invariant under congruence of configurations
-- statement:
--   For $n\in\mathbb{N}$ let $\mathbb{R}^n$ denote $n$-dimensional Euclidean space with the Euclidean distance $\|p-q\|$ between points $p,q$. A *configuration* of $s$ points in $\mathbb{R}^d$ is an indexed family $a=(a_0,\dots,a_{s-1})$ of points $a_i\in\mathbb{R}^d$. Two configurations $a$ in $\mathbb{R}^d$ and $b$ in $\mathbb{R}^D$ with the same index set are *congruent* if
--   $$\|b_i-b_j\|=\|a_i-a_j\|\qquad\text{for all } i,j\in\{0,\dots,s-1\};$$
--   the dimensions $d$ and $D$ may differ. A configuration $a$ is *Ramsey* if for every integer $r\ge 2$ there is a dimension $n\ge 1$ such that every colouring $c:\mathbb{R}^n\to\{0,1,\dots,r-1\}$ admits a configuration $x$ in $\mathbb{R}^n$ congruent to $a$ and a colour $k$ with $c(x_i)=k$ for every $i$ (a monochromatic congruent copy of $a$).
--
--   **Theorem.** Let $s,d,D\in\mathbb{N}$, let $a$ be a configuration of $s$ points in $\mathbb{R}^d$ and $b$ a configuration of $s$ points in $\mathbb{R}^D$, and suppose that $a$ and $b$ are congruent. Then
--   $$a\ \text{is Ramsey}\iff b\ \text{is Ramsey}.$$
--
--   Whether a configuration is Ramsey therefore depends only on its list of mutual distances, not on its position or on the dimension of the space in which it is drawn. This lets one replace a configuration by any convenient congruent representative, for instance one whose points affinely span the ambient space, before applying a criterion that requires such a normal form.
--
--   **Formalization Note** Points are elements of `Space d = EuclideanSpace ℝ (Fin d)` and configurations are maps `Fin s → Space d`. `Congruent a b` is `∀ i j, dist (b i) (b j) = dist (a i) (a j)` and `Ramsey a` is `∀ r, 2 ≤ r → ∃ D, 1 ≤ D ∧ ∀ c : Space D → Fin r, ∃ b, Congruent a b ∧ ∃ k, ∀ i, c (b i) = k`. No injectivity of $a$ or $b$ and no lower bound on $s$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Congruence.lean#L24-L36

import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model

open OAI OAI.EuclideanRamsey
universe uIndex uDomain uCodomain
open scoped TensorProduct RealInnerProductSpace

theorem OAI.EuclideanRamsey.ramsey_congruent_iff {s d D : ℕ} {a : Fin s → Space d}
    {b : Fin s → Space D} (h : Congruent a b) : Ramsey a ↔ Ramsey b := by sorry
