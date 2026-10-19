-- Prove2me | Theorems.Thm_OAI_FiniteCircle_mask_minimizer_options
-- name    : OAI.FiniteCircle.mask_minimizer_options
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T13:37:07.731244+00:00
-- url     : https://prove2.me/theorems/ccc49268-a09d-476b-b0f0-ec266b13e331
-- title:
--   A minimizing mask residue vector obeys both the reset and the descent lower bound
-- statement:
--   Let $f$ be a *phase cost* on $\mathbb{Z}_M=\mathbb{Z}/M\mathbb{Z}$, i.e. $f\ge0$, $f(0)=0$, $f(-x)=f(x)$ and $f(x+y)\le f(x)+f(y)$. Fix $h\ge1$ and primes $p_0,\dots,p_{h-1}$ dividing $M$ with $h^3\le p_k\le 2h^3$, and let $\iota_k:\mathbb{Z}_{p_k}\to\mathbb{Z}_M$ be $a\mapsto(M/p_k)\,a$. For a residue vector $z\in\prod_{k<h}\mathbb{Z}_{p_k}$ let $S(z)=\{k:z_k\ne0\}$ be its active set. With the tag set $J=\{(k,b):0\le k<h,\ 0\le b<p_k\}$ and the mask phase map $\sigma(z)_{(k,b)}=\sum_{k'<h}\iota_{k'}(z_{k'})+b\,\iota_k(z_k)$ define the average cost $A_f(x,z)=\frac1{|J|}\sum_{j\in J}f(x+\sigma(z)_j)$ and the *minimized average*
--
--   $$
--   f^{\sigma}(x)=\min_{z\in\prod_k\mathbb{Z}_{p_k}}A_f(x,z).
--   $$
--
--   **Theorem.** For every $x\in\mathbb{Z}_M$ there is a residue vector $z$ such that, with $S=S(z)$:
--
--   1. for every real $Q\ge0$ with $Q\le f(\iota_k(1))$ for all $k\in S$,
--   $$
--   \frac{|S|}{4h}\,Q\le f^{\sigma}(x);
--   $$
--   2. if $2|S|\le h$, then
--   $$
--   \frac14\,f\Bigl(x+\sum_{k<h}\iota_k(z_k)\Bigr)\le f^{\sigma}(x).
--   $$
--
--   The hierarchical mask costs are defined by iterating $c_{l+1}=(c_l)^{\sigma_{l+1}}$, and the lemma gives, for one residue vector at which the minimum is attained, both alternatives at once: a "reset" bound through the costs of the basic steps $\iota_k(1)$, and a "descent" bound through the cost of the translated phase. A case analysis on the size of $S$ then drives the inductive lower bound for mask costs.
--
--   **Formalization Note** $f^{\sigma}(x)$ is `f.infAverage (maskPhaseHom h p M l hd) x`, the infimum over the finite group `MaskResidues h p l`. Besides the explicit hypotheses the theorem takes the instance `[∀ k, NeZero (p l k)]` (each $p_k\ne0$; this makes the residue group finite and is implied by primality). No assumption $M\ne0$ is made.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/MaskSeparation.lean#L191-L213

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

theorem OAI.FiniteCircle.mask_minimizer_options {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    [∀ k : Fin h, NeZero (p l k)]
    (hh : 0 < h) (hd : ∀ k : Fin h, p l k ∣ M)
    (hp : ∀ k : Fin h, (p l k).Prime)
    (hlo : ∀ k : Fin h, h^3 ≤ p l k) (hhi : ∀ k : Fin h, p l k ≤ 2*h^3)
    (f : PhaseCost (ZMod M)) (x : ZMod M) :
    ∃ z : MaskResidues h p l,
      (let S := Finset.univ.filter (fun k : Fin h => z k ≠ 0)
       (∀ Q : ℝ, 0 ≤ Q → (∀ k ∈ S, Q ≤ f (subcircle (hd k) 1)) →
        (S.card : ℝ)/(4*h)*Q ≤ f.infAverage (maskPhaseHom h p M l hd) x) ∧
       (2*S.card ≤ h → (1/4:ℝ)*f (x+∑ k,subcircle (hd k) (z k)) ≤
         f.infAverage (maskPhaseHom h p M l hd) x)) := by sorry
