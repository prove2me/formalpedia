-- Prove2me | Theorems.Thm_InvariantMean_not_exists_translationInvariant_normalised_functional_int
-- name    : InvariantMean.not_exists_translationInvariant_normalised_functional_int
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-22T10:08:27.764735+00:00
-- url     : https://prove2.me/theorems/7c78c892-f6d1-495b-a4d7-eaf7af464a3b
-- title:
--   No translation-invariant normalised functional on all real functions on the integers
-- statement:
--   There is no $\mathbb{R}$-linear functional $m$ on the space of **all** real-valued
--   functions on $\mathbb{Z}$ that is both translation-invariant and normalised.
--
--   Precisely, no $m$ satisfies both
--
--   - $m\bigl(n \mapsto f(n-1)\bigr) = m(f)$ for every $f : \mathbb{Z} \to \mathbb{R}$, and
--   - $m(\mathbf{1}) = 1$, where $\mathbf{1}$ is the constant function with value $1$.
--
--   Invariance is imposed only for the one-step shift. For a linear functional on $\mathbb{Z}$ that
--   is equivalent to invariance under every translation, since the shift by one generates them all,
--   so nothing is lost by stating the weaker hypothesis — and the theorem is correspondingly
--   stronger.
--
--   The domain is the full function space, with no boundedness condition, and $m$ is required only
--   to be linear: **no positivity, continuity or norm condition appears**. The statement is
--   therefore stronger than the corresponding failure for an invariant *mean*, which would in
--   addition be positive — not even a bare linear functional survives here.
--
--   The obstruction is the unbounded function $n \mapsto n$. Its translate $n \mapsto n-1$ differs
--   from it by the constant function $\mathbf{1}$, so invariance and linearity together force
--   $m(\mathbf{1})$ to be $0$, contradicting normalisation.
--
--   This is the reason an invariant mean is defined on $\ell^\infty(G)$ rather than on all
--   functions: widening the domain does not merely cost positivity, it makes the notion
--   unsatisfiable. The argument shown here needs a function whose translate differs from it by a
--   nonzero constant, which $\mathbb{Z}$ supplies; it is not a claim about every infinite group.
-- source:
--   Not a result from a source text. This records the convention committed to by the mission "Garrido Amenable Groups I: Invariant Means and the Folner Condition": that an invariant mean is taken on the bounded functions, and not on all real-valued functions on the group. The observation is standard and the witness used here (the unbounded identity on the integers, whose translate differs from it by a constant) is the usual one; no published source is claimed for it.

import Mathlib

namespace InvariantMean

theorem not_exists_translationInvariant_normalised_functional_int :
    ¬ ∃ m : (ℤ → ℝ) →ₗ[ℝ] ℝ,
      (∀ f : ℤ → ℝ, m (fun n => f (n - 1)) = m f) ∧ m (fun _ => (1 : ℝ)) = 1 := by
  sorry

end InvariantMean
