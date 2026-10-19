-- Prove2me | Theorems.Thm_OAI_FiniteCircle_excluded_minimizer_options
-- name    : OAI.FiniteCircle.excluded_minimizer_options
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:39:37.602282+00:00
-- url     : https://prove2.me/theorems/8126481d-052b-4dae-82d6-f4e9cd06fa3f
-- title:
--   A minimizing excluded-sum residue vector obeys both the reset and the descent lower bound
-- statement:
--   Let $f$ be a *phase cost* on $\mathbb{Z}_M=\mathbb{Z}/M\mathbb{Z}$: $f\ge0$, $f(0)=0$, $f(-x)=f(x)$ and $f(x+y)\le f(x)+f(y)$. Fix $m\ge2$ and positive integers $p_0,\dots,p_{m-1}$ dividing $M$, let $\iota_k:\mathbb{Z}_{p_k}\to\mathbb{Z}_M$ be $a\mapsto(M/p_k)\,a$, and for a residue vector $z\in\prod_{k<m}\mathbb{Z}_{p_k}$ let $A(z)=\{k:z_k\ne0\}$ be its active set. With the excluded phase map $\tau(z)_i=\sum_{j<m,\ j\ne i}\iota_j(z_j)$ ($0\le i<m$) define
--
--   $$
--   f^{\tau}(x)=\min_{z\in\prod_k\mathbb{Z}_{p_k}}\ \frac1m\sum_{i<m}f\bigl(x+\tau(z)_i\bigr).
--   $$
--
--   **Theorem.** For every $x\in\mathbb{Z}_M$ there is a residue vector $z$, with active set $A=A(z)$, such that
--
--   1. for every real $Q\ge0$ with $Q\le f\bigl(\iota_i(z_i)-\iota_j(z_j)\bigr)$ whenever $z_i\ne0$ and $i\ne j$,
--   $$
--   \frac{|A|}{4m}\,Q\le f^{\tau}(x);
--   $$
--   2. if $2|A|\le m$, then
--   $$
--   \frac14\,f\Bigl(x+\sum_{k<m}\iota_k(z_k)\Bigr)\le f^{\tau}(x).
--   $$
--
--   The hierarchical excluded-sum costs are obtained by iterating $e_{l+1}=(e_l)^{\tau_{l+1}}$, and the lemma provides, for one residue vector at which the minimum is attained, both a "reset" bound through the costs of the pairwise differences and a "descent" bound through the cost of the translated phase. It is the excluded-sum counterpart of the corresponding statement for mask costs.
--
--   **Formalization Note** $f^{\tau}$ is `f.step (excludedPhaseHom m p M l hd)`, itself a phase cost, evaluated at `x`. Positivity of the $p_k$ appears twice, as the instance `[∀ k, NeZero (p l k)]` (needed for the residue group to be finite) and as the hypothesis `hn`. No primality of the $p_k$ and no assumption $M\ne0$ is made.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/ExcludedSeparation.lean#L131-L153

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

theorem OAI.FiniteCircle.excluded_minimizer_options {m M l : ℕ} {p : ℕ → ℕ → ℕ}
    [∀ k : Fin m, NeZero (p l k)]
    (hm : 2 ≤ m) (hd : ∀ k : Fin m, p l k ∣ M) (hn : ∀ k : Fin m, 0 < p l k)
    (f : PhaseCost (ZMod M)) (x : ZMod M) :
    ∃ z : MaskResidues m p l,
      (∀ Q : ℝ, 0 ≤ Q → (∀ i j : Fin m, z i ≠ 0 → i ≠ j →
        Q ≤ f (subcircle (hd i) (z i)-subcircle (hd j) (z j))) →
        (((Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card : ℝ)/(4*m))*Q ≤
          (f.step (excludedPhaseHom m p M l hd)) x) ∧
      (2*(Finset.univ.filter (fun k : Fin m => z k ≠ 0)).card ≤ m →
        (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
          (f.step (excludedPhaseHom m p M l hd)) x) := by sorry
