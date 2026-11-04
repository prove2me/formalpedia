-- Prove2me | Theorems.Thm_OAI_SignedSweeps_signed_occurrence_moment_bound_proved_ranges
-- name    : OAI.SignedSweeps.signed_occurrence_moment_bound_proved_ranges
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T00:28:47.268968+00:00
-- url     : https://prove2.me/theorems/19a893a1-f851-42d3-9edf-b0a5e0ec7f32
-- title:
--   Signed occurrence moment bound on the non-inductive ranges
-- statement:
--   This records the ranges of representations in which the moment bound of the signed sweep needs no induction: finitely many sizes, sparse levels, level one, and shapes with too many rows.
--
--   Let $n=2^d$ with $d\ge 1$, identify $\{0,\dots,n-1\}$ with binary strings of length $d$, and for a partition $\lambda\vdash n$ let $S^\lambda$ be the Specht module, $D_\lambda=\dim S^\lambda$. Write $\Pi_i$ for the average over the permutations preserving every binary coordinate except the $i$-th, $T_\lambda$ for the product of the $\Pi_i$ in reverse coordinate order, and
--
--   $$J_r(\lambda)=D_\lambda\,\operatorname{Re}\operatorname{Tr}_{S^\lambda}\big((T_\lambda^*T_\lambda)^r\big).$$
--
--   For $u+v+l=n$ and $\alpha\vdash u$, $\beta\vdash v$, $\gamma\vdash l$, a *signed occurrence* is an injective map $S^\alpha\otimes S^{\beta^t}\otimes S^\gamma\to S^\lambda$ intertwining $S_u\times S_v\times S_l$. Put
--
--   $$F(\alpha,\beta)=\sum_{a\in\alpha}a\log\frac{u+v}{a}+\sum_{b\in\beta}b\log\frac{u+v}{b},\qquad c_a(d)=a\Big(1-\frac1{2\sqrt d}\Big),$$
--
--   $$g_\kappa(d,l)=\max\{0,\ c_\kappa(d)\,l\log n-l\log(n/l)\}\quad(l>0),\qquad g_\kappa(d,0)=0.$$
--
--   Let $D\in\mathbb{N}$, $\delta>0$, $\eta\ge0$ and $\kappa\in\mathbb{R}$. Then there is $r_0\ge1$ such that for all $r\ge r_0$, all $d\ge1$, and all $\lambda\vdash n=2^d$ satisfying at least one of
--
--   - $d\le D$,
--   - $n-\lambda_1\le n^{1-\delta}$,
--   - $n-\lambda_1=1$,
--   - $\lambda$ has more than $n/2$ rows,
--
--   every signed occurrence of $(\alpha,\beta,\gamma)$ in $\lambda$ satisfies
--
--   $$
--   \log J_r(\lambda)\le c_\eta(d)\,F(\alpha,\beta)+g_\kappa(d,l).
--   $$
--
--   In fact the proof gives $J_r(\lambda)\le1$ in each of these ranges, and the right side is nonnegative.
--
--   Here the sum in $F$ runs over all parts of $\alpha$ and all parts of $\beta$, counted with multiplicity. The logarithm of $0$ is $-\infty$, which is the relevant case when $J_r(\lambda)=0$.
--
--   **Formalization Note** The upstream statement is reproduced verbatim from `ProvedRanges.lean`. Here $\kappa$ is an arbitrary real, for which the Lean definition of $g_\kappa$ is still nonnegative.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Sections 4.1 and 4.2, eq. (17), and Lemma 2.2. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/ProvedRanges.lean#L34-L59

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators

theorem signed_occurrence_moment_bound_proved_ranges (D : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (κ : ℝ) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r ≥ r₀, ∀ d : ℕ, 1 ≤ d →
      ∀ lam : Partition (2 ^ d),
        (d ≤ D ∨
          ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) ∨
          2 ^ d - lam.1.rowLen 0 = 1 ∨
          2 ^ d / 2 < lam.1.colLen 0) →
        ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
          (α : Partition u) (β : Partition v) (γ : Partition l),
          SignedOccurrence h α β γ lam →
          logMoment (weightedMoment lam r) ≤
            ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal) := by sorry

end SignedSweeps
end
end OAI
