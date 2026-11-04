-- Prove2me | Theorems.Thm_OAI_SignedSweeps_signed_occurrence_moment_bound_fixed
-- name    : OAI.SignedSweeps.signed_occurrence_moment_bound_fixed
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T00:29:25.065896+00:00
-- url     : https://prove2.me/theorems/d8e75fda-0daa-4c61-87b6-148fa3d5153e
-- title:
--   Moment bound for every signed occurrence, with fixed constants
-- statement:
--   This is the every-occurrence moment bound of the source with its constants fixed, the form in which the strong induction runs.
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
--   Let $0<\eta<1$ and $0<\kappa<\eta/256$. Then there is an integer $r\ge1$ such that for all $d\ge1$, all $\lambda\vdash2^d$, and every signed occurrence of $(\alpha,\beta,\gamma)$ in $\lambda$,
--
--   $$
--   \log J_r(\lambda)\le c_\eta(d)\,F(\alpha,\beta)+g_\kappa(d,l),
--   $$
--
--   where the logarithm of $0$ is $-\infty$. The integer $r$ depends only on $\eta$ and $\kappa$.
--
--   This is the content of eq. (3) in Theorem 1.1 of the source, with the smallness conditions on the constants made explicit.
--
--   Here the sum in $F$ runs over all parts of $\alpha$ and all parts of $\beta$, counted with multiplicity.
--
--   **Formalization Note** The upstream statement is reproduced verbatim from `UniformMoment.lean`. The comparison is in the extended reals.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Section 4, proof of Theorem 1.1, eq. (3). Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/UniformMoment.lean#L40-L126

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

theorem signed_occurrence_moment_bound_fixed {η κ : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hsmall : κ < η/256) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ d : ℕ, 1 ≤ d →
      ∀ lam : Partition (2^d), ∀ (u v l : ℕ) (h : u+v+l=2^d)
        (α : Partition u) (β : Partition v) (γ : Partition l),
        SignedOccurrence h α β γ lam →
        logMoment (weightedMoment lam r) ≤
          ((coefficient η d*signedEntropy α β+remainderBudget κ d l : ℝ) : EReal) := by sorry

end SignedSweeps
end
end OAI
