-- Prove2me | Theorems.Thm_ImpatientQPTAS_reduction
-- name    : ImpatientQPTAS.reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:56.259199+00:00
-- url     : https://prove2.me/theorems/2382145b-5a6a-424a-b8f6-b663a9452e57
-- title:
--   §2.1, p.8 — the reduction to average customers (repaired)
-- statement:
--   Let $\epsilon\in(0,\tfrac14)$ and $e=1/\lceil16/\epsilon\rceil$. For every instance, every adaptive service policy $S$ satisfies
--   $$
--   (1-6e)\,R(S)\le X+\sum_{i\in C_{\mathrm{stick}}}r_i ,
--   $$
--   where $X$ is $X^{\rho}$ at the true rewards, and the computed policy $\tilde S$ satisfies
--   $$
--   \tilde X+(1-4e)\sum_{i\in C_{\mathrm{stick}}}r_i\le R(\tilde S).
--   $$
--
--   This plays the role of Lemma 2.2 for the policy the program computes: both sides are in terms of the true rewards and probabilities.
--
--   **Formalization Note** Lemma 2.2 is not stated: its family of policies $S^{\approx A}$, one per subset, cannot be evaluated within the time bound.
--
--   Differences from the source:
--   - reading: Lemma 2.2: R(S) ≥ (1 − 7ε)·R(S*) for the black-box reduction with policies S^≈A → two inequalities through X and X̃, for the computed policy; reason: the black-box form needs a per-set rounding whose first move cannot be evaluated; these inequalities give the same conclusion for the program
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, §2.1, p.8; Lemma 2.1, p.8; Lemma 2.2, p.8; App. A.1–A.2

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes
import Definitions.Def_ImpatientQPTAS_Rounding
import Definitions.Def_ImpatientQPTAS_Program

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, §2.1, p.8, repaired: the reduction to average customers, in the form the
program needs. With `e = accuracy ε`, every adaptive policy satisfies
`(1 − 6e)·R(S) ≤ X + Σ_{i ∈ C_stick} r_i`, and the computed policy satisfies
`X̃ + (1 − 4e)·Σ_{i ∈ C_stick} r_i ≤ R(S̃)`, on the true rewards and probabilities.

**Formalization Note.** `X` is `Xval` at the true rewards. This takes the place of Lemma 2.2, whose
family of per-set policies cannot be evaluated in quasi-polynomial time. -/
theorem reduction {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) (I : Instance n)
    (hI : I.Standing) :
    (∀ S : Policy n, IsPolicy S →
      (1 - 6 * accuracy ε) * I.R S ≤
        Xval (accuracy ε) I I.r + ∑ i ∈ Cstick (accuracy ε) I, I.r i) ∧
    Xt (accuracy ε) I + (1 - 4 * accuracy ε) * ∑ i ∈ Cstick (accuracy ε) I, I.r i ≤
      I.R (policy ε I) := by sorry

end ImpatientQPTAS
