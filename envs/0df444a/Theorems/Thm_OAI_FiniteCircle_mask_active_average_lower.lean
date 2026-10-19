-- Prove2me | Theorems.Thm_OAI_FiniteCircle_mask_active_average_lower
-- name    : OAI.FiniteCircle.mask_active_average_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:35:45.713869+00:00
-- url     : https://prove2.me/theorems/d1ac6c5e-e394-4387-8c4e-9c3e9413fe2c
-- title:
--   Active mask coordinates force a large average phase cost
-- statement:
--   Let $G$ be an abelian group. A *phase cost* on $G$ is a function $f:G\to\mathbb{R}$ such that $f(x)\ge0$, $f(0)=0$, $f(-x)=f(x)$ and $f(x+y)\le f(x)+f(y)$ for all $x,y\in G$.
--
--   Fix natural numbers $h\ge1$ and $M$, and primes $p_0,\dots,p_{h-1}$ with $p_k\mid M$ and $h^3\le p_k\le 2h^3$ for every $k$. Write $\mathbb{Z}_n=\mathbb{Z}/n\mathbb{Z}$ and let $\iota_k:\mathbb{Z}_{p_k}\to\mathbb{Z}_M$ be the homomorphism $a\mapsto (M/p_k)\,a$. A *residue vector* is $z=(z_0,\dots,z_{h-1})\in\prod_{k<h}\mathbb{Z}_{p_k}$, with *active set* $S(z)=\{k: z_k\neq0\}$. The *tags* are the pairs $(k,b)$ with $0\le k<h$ and $0\le b<p_k$; they form a set $J$ of size $|J|=\sum_k p_k$. The *mask phase map* is the homomorphism $\sigma:\prod_k\mathbb{Z}_{p_k}\to(\mathbb{Z}_M)^J$,
--
--   $$
--   \sigma(z)_{(k,b)}=\sum_{k'<h}\iota_{k'}(z_{k'})+b\,\iota_k(z_k),
--   $$
--
--   and for a phase cost $f$ on $\mathbb{Z}_M$ and $x\in\mathbb{Z}_M$ the *average cost* of $z$ at $x$ is $A_f(x,z)=\frac{1}{|J|}\sum_{j\in J}f\bigl(x+\sigma(z)_j\bigr)$.
--
--   **Theorem.** Let $f$ be a phase cost on $\mathbb{Z}_M$, $x\in\mathbb{Z}_M$, $z$ a residue vector and $Q\ge0$ a real number with $Q\le f(\iota_k(1))$ for every active index $k\in S(z)$. Then
--
--   $$
--   \frac{|S(z)|}{4h}\,Q\le A_f(x,z).
--   $$
--
--   For an active index $k$ the points $x+\sigma(z)_{(k,b)}$, $0\le b<p_k$, run through a full coset of the subgroup $\iota_k(\mathbb{Z}_{p_k})$ (because $p_k$ is prime), so they cannot all be cheap when the basic step $\iota_k(1)$ is expensive. In the recursion $c_{l+1}(x)=\min_z A_{c_l}(x,z)$ that defines the hierarchical mask costs, this is the "reset" alternative: a minimizing residue vector with many active coordinates gives a lower bound in terms of the costs $c_l(\iota_k(1))$.
--
--   **Formalization Note** The primes are the level-$l$ entries `p l k` of a table `p : ℕ → ℕ → ℕ`; residue vectors are `MaskResidues h p l`, $\iota_k$ is `subcircle (hd k)`, $\sigma$ is `maskPhaseHom h p M l hd`, and $A_f(x,z)$ is `f.average σ x z`. The product $b\,\iota_k(z_k)$ is the natural-number multiple `b.val • _`. No assumption $M\ne0$ is made (for $M=0$, `ZMod 0` is the integers).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/MaskSeparation.lean#L85-L139

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.mask_active_average_lower {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hh : 0 < h) (hd : ∀ k : Fin h, p l k ∣ M)
    (hp : ∀ k : Fin h, (p l k).Prime)
    (hlo : ∀ k : Fin h, h^3 ≤ p l k) (hhi : ∀ k : Fin h, p l k ≤ 2*h^3)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues h p l)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hq : ∀ k : Fin h, z k ≠ 0 → Q ≤ f (subcircle (hd k) 1)) :
    (((Finset.univ.filter (fun k : Fin h => z k ≠ 0)).card : ℝ)/(4*h))*Q ≤
      f.average (maskPhaseHom h p M l hd) x z := by sorry
