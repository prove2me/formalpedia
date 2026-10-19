-- Prove2me | Theorems.Thm_OAI_FiniteCircle_mask_inactive_average_lower
-- name    : OAI.FiniteCircle.mask_inactive_average_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:36:30.520341+00:00
-- url     : https://prove2.me/theorems/cfb2533d-4d81-49f9-a3f0-2b78de331a02
-- title:
--   Mostly inactive mask residues retain a quarter of the translated phase cost
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
--   **Theorem.** Let $f$ be a phase cost on $\mathbb{Z}_M$, $x\in\mathbb{Z}_M$ and $z$ a residue vector with at most half of its coordinates nonzero, $2\,|S(z)|\le h$. Then
--
--   $$
--   \frac14\,f\Bigl(x+\sum_{k<h}\iota_k(z_k)\Bigr)\le A_f(x,z).
--   $$
--
--   This is the "descent" alternative in the analysis of the hierarchical mask costs $c_{l+1}(x)=\min_zA_{c_l}(x,z)$: if a minimizing residue vector has few active coordinates, then the next-level cost at $x$ is at least a quarter of the previous-level cost at the translated phase $x+\sum_k\iota_k(z_k)$. Together with the companion bound for many active coordinates it yields a dichotomy for every minimizer.
--
--   **Formalization Note** As in the companion lemma, the primes are the level-$l$ entries `p l k`, residue vectors are `MaskResidues h p l`, $\iota_k$ is `subcircle (hd k)` and $A_f$ is `f.average (maskPhaseHom h p M l hd)`. No assumption $M\ne0$ is made.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/MaskSeparation.lean#L141-L189

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

theorem OAI.FiniteCircle.mask_inactive_average_lower {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hh : 0 < h) (hd : ∀ k : Fin h, p l k ∣ M)
    (hp : ∀ k : Fin h, (p l k).Prime)
    (hlo : ∀ k : Fin h, h^3 ≤ p l k) (hhi : ∀ k : Fin h, p l k ≤ 2*h^3)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues h p l)
    (hs : 2*(Finset.univ.filter (fun k : Fin h => z k ≠ 0)).card ≤ h) :
    (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
      f.average (maskPhaseHom h p M l hd) x z := by sorry
