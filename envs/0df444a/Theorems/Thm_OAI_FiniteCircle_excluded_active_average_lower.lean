-- Prove2me | Theorems.Thm_OAI_FiniteCircle_excluded_active_average_lower
-- name    : OAI.FiniteCircle.excluded_active_average_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:38:47.378124+00:00
-- url     : https://prove2.me/theorems/d31d2553-30ab-497a-8369-0d1c752afc36
-- title:
--   Pairwise expensive differences force a large excluded-sum average cost
-- statement:
--   Let $G$ be an abelian group. A *phase cost* on $G$ is a function $f:G\to\mathbb{R}$ such that $f(x)\ge0$, $f(0)=0$, $f(-x)=f(x)$ and $f(x+y)\le f(x)+f(y)$ for all $x,y\in G$.
--
--   Fix natural numbers $m\ge2$ and $M$, and natural numbers $p_0,\dots,p_{m-1}$ dividing $M$. With $\mathbb{Z}_n=\mathbb{Z}/n\mathbb{Z}$ let $\iota_k:\mathbb{Z}_{p_k}\to\mathbb{Z}_M$ be the homomorphism $a\mapsto(M/p_k)\,a$. For a residue vector $z\in\prod_{k<m}\mathbb{Z}_{p_k}$ let $A(z)=\{k:z_k\ne0\}$ be its active set, and define the *excluded phase map* $\tau:\prod_k\mathbb{Z}_{p_k}\to(\mathbb{Z}_M)^m$ by
--
--   $$
--   \tau(z)_i=\sum_{j<m,\ j\ne i}\iota_j(z_j)\qquad(0\le i<m),
--   $$
--
--   the sum of all embedded residues except the $i$-th. For a phase cost $f$ on $\mathbb{Z}_M$ and $x\in\mathbb{Z}_M$ put $E_f(x,z)=\frac1m\sum_{i<m}f\bigl(x+\tau(z)_i\bigr)$.
--
--   **Theorem.** Let $f$ be a phase cost on $\mathbb{Z}_M$, $x\in\mathbb{Z}_M$, $z$ a residue vector and $Q\ge0$ a real number such that $Q\le f\bigl(\iota_i(z_i)-\iota_j(z_j)\bigr)$ whenever $z_i\ne0$ and $j\ne i$. Then
--
--   $$
--   \frac{|A(z)|}{4m}\,Q\le E_f(x,z).
--   $$
--
--   The points $x+\tau(z)_i$ and $x+\tau(z)_j$ differ by $\iota_i(z_i)-\iota_j(z_j)$, so the hypothesis prevents an active point and any other point from both being cheap. In the recursion $e_{l+1}(x)=\min_zE_{e_l}(x,z)$ defining the hierarchical excluded-sum costs, this is the "reset" alternative for a minimizing residue vector with many active coordinates.
--
--   **Formalization Note** The $p_k$ are the level-$l$ entries `p l k` of a table `p : ℕ → ℕ → ℕ`, residue vectors are `MaskResidues m p l`, $\tau$ is `excludedPhaseHom m p M l hd`, and $E_f(x,z)$ is `f.average τ x z`. No primality, size or positivity condition on the $p_k$ and no assumption $M\ne0$ is needed (Lean's `ZMod 0` is the integers).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/ExcludedSeparation.lean#L51-L100

import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation

open OAI OAI.FiniteCircle
open scoped BigOperators List

theorem OAI.FiniteCircle.excluded_active_average_lower {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hm : 2 ≤ m) (hd : ∀ k : Fin m, p l k ∣ M)
    (f : PhaseCost (ZMod M)) (x : ZMod M) (z : MaskResidues m p l)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hq : ∀ i j : Fin m, z i ≠ 0 → i ≠ j →
      Q ≤ f (subcircle (hd i) (z i)-subcircle (hd j) (z j))) :
    (((Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card : ℝ)/(4*m))*Q ≤
      f.average (excludedPhaseHom m p M l hd) x z := by sorry
