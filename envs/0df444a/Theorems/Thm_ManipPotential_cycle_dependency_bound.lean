-- Prove2me | Theorems.Thm_ManipPotential_cycle_dependency_bound
-- name    : ManipPotential.cycle_dependency_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:46:07.481485+00:00
-- url     : https://prove2.me/theorems/4aa4281d-5315-4f9f-9802-7e6aa4ed7aa9
-- title:
--   Proof of Theorem 6.1, final steps — comparison vectors around the cycle force $\lambda \ge m-1$
-- statement:
--   Let $m \ge 3$ and $\lambda > 1$ be real. Let $W \subseteq \mathbb R^{m!}$ be a linear subspace of dimension $m - 1$, and for each $i \in [m]$ (indices modulo $m$) let $w_i \in W \cap C_{i, i+1}$ satisfy $w_i \cdot (\ell_i - \ell_{i+1}) = 1$, where $C_{i,i+1}$ is the comparison cone (18)–(19) with constant $\lambda$. Then
--   $$
--   \lambda \ \ge\ m - 1 .
--   $$
--
--   This is the linear-algebra core of the last part of the proof of Theorem 6.1, applied to the comparison vectors of Proposition 6.12 along the cycle $c_1 \to c_2 \to \cdots \to c_m \to c_1$ with $\lambda = K + 1$.
--
--   Differences from the source:
--   - generalization: λ = K + 1 and w_i = w_{i,i+1} the comparison vectors of Proposition 6.12 → any real λ > 1, any (m − 1)-dimensional W and any w_i ∈ W ∩ C_{i,i+1} with w_i · (ℓ_i − ℓ_{i+1}) = 1; reason: the final steps use only these properties; the paper's vectors satisfy them
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), proof of Theorem 6.1, final steps, pp.37–38

import Mathlib
import Definitions.Def_ManipPotential_Cmp
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec

namespace ManipPotential

/-- The final steps of the proof of Theorem 6.1 (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), proof of Theorem 6.1, final steps,
pp.37–38): if `λ > 1`, `W ⊆ ℝ^{m!}` has dimension `m − 1`, and for every `i` the vector
`w_i ∈ W ∩ C_{i,i+1}` satisfies `w_i · (ℓ_i − ℓ_{i+1}) = 1` (indices mod `m`), then `λ ≥ m − 1`. -/
theorem cycle_dependency_bound {m : ℕ} [NeZero m] (hm : 3 ≤ m) (lam : ℝ) (hlam : 1 < lam)
    (W : Submodule ℝ (Ranking m → ℝ)) (hW : Module.finrank ℝ W = m - 1)
    (w : Fin m → Ranking m → ℝ) (hwW : ∀ i, w i ∈ W) (hwC : ∀ i, w i ∈ Cmp lam i (i + 1))
    (hwn : ∀ i, dotProduct (w i) (unitVec (ell i) - unitVec (ell (i + 1))) = 1) :
    (m : ℝ) - 1 ≤ lam := by sorry

end ManipPotential
