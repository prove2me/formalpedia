-- Prove2me | Theorems.Thm_MonotoneCompStatics_LinearPerturb_theorem10_first_sentence
-- name    : MonotoneCompStatics.LinearPerturb.theorem10_first_sentence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:18.287813+00:00
-- url     : https://prove2.me/theorems/83f18d51-9869-4a3d-b56d-e7f0679c92b7
-- title:
--   Theorem 10, first sentence — f + p·x is quasisupermodular with single crossing for all p iff f is supermodular
-- statement:
--   Let $n \ge 0$ and $f : \mathbb{R}^n \times \mathbb{R} \to \mathbb{R}$, $(x, t) \mapsto f(x, t)$. Order $\mathbb{R}^n$ componentwise and $\mathbb{R}^n \times \mathbb{R}$ by the product order, so that joins and meets are componentwise maxima and minima. Write $p \cdot x = \sum_i p_i x_i$. Then the following are equivalent:
--
--   1. for every $p \in \mathbb{R}^n$, the function $(x, t) \mapsto f(x, t) + p \cdot x$ is quasisupermodular in $x$ (for each fixed $t$) and has the single crossing property in $(x; t)$;
--   2. $f$ is supermodular on the lattice $\mathbb{R}^n \times \mathbb{R}$:
--   $$
--   f(z) + f(z') \le f(z \vee z') + f(z \wedge z') \qquad \text{for all } z, z' \in \mathbb{R}^n \times \mathbb{R}.
--   $$
--
--   The theorem says that supermodularity, although never necessary for monotone comparative statics, is exactly what is needed when the objective must behave well under every linear price perturbation $p \cdot x$ of the choice variables.
--
--   **Formalization Note** $f$ is curried, `f : (Fin n → ℝ) → ℝ → ℝ`. "$f$ is supermodular" is read as supermodularity jointly in $(x, t)$ on $\mathbb{R}^n \times \mathbb{R}$ (the published `SupermodularOn` applied to $(x,t) \mapsto f(x,t)$ with `Set.univ`), as the paper's proof confirms ("If $f$ is supermodular in $(x, t)$ …"); supermodularity in $x$ alone would not imply the single crossing property. "Quasisupermodular in $x$" means quasisupermodular on $\mathbb{R}^n$ for every fixed $t$. The quantifier over $p$ covers both properties.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), p. 166 (PDF p. 11), Theorem 10, first sentence

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing

namespace MonotoneCompStatics.LinearPerturb

/-- Milgrom and Shannon (1994), p. 166, Theorem 10, first sentence: for `f : ℝⁿ × ℝ → ℝ`,
`f(x, t) + p · x` is quasisupermodular in `x` and has the single crossing property in `(x; t)`
for all `p ∈ ℝⁿ` if and only if `f` is supermodular (jointly in `(x, t)`, on the product lattice
`ℝⁿ × ℝ`). -/
theorem theorem10_first_sentence {n : ℕ} (f : (Fin n → ℝ) → ℝ → ℝ) :
    (∀ p : Fin n → ℝ, (∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => f x t + p ⬝ᵥ x) Set.univ) ∧
        MonotoneCompStatics.Monotonicity.SingleCrossing (fun x t => f x t + p ⬝ᵥ x)) ↔
      Supermodularity.Monotonicity.SupermodularOn
        (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ := by sorry

end MonotoneCompStatics.LinearPerturb
