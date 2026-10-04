-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Continuous_const_on_crit_component
-- name    : NonsmoothLojasiewicz.Continuous.const_on_crit_component
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:15:12.356327+00:00
-- url     : https://prove2.me/theorems/ffb44d21-655d-4e60-aae1-80083122bf8a
-- title:
--   Eq. (6) (recalled from [5, Theorem 13]): $f$ is constant on the connected component of $\mathrm{crit}\, f$ through $a$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R} \cup \{+\infty\}$ be subanalytic, with closed domain, and continuous relative to its domain. Let $a \in \operatorname{crit} f$ and let $(\operatorname{crit} f)_a$ be the connected component of $\operatorname{crit} f$ containing $a$. Then
--   $$
--   f(x) = f(a) \qquad \text{for every } x \in (\operatorname{crit} f)_a .
--   $$
--
--   This is a nonsmooth Morse–Sard type statement, recalled by the paper from Bolte, Daniilidis and Lewis, *A Sard theorem for non-differentiable functions*, J. Math. Anal. Appl. 321 (2006). It is used in the proof of Theorem 3.1 to ensure $f \equiv f(a)$ on the critical component through $a$.
--
--   **Formalization Note.** `connectedComponentIn (crit f) a` is the connected component of `a` in the subspace `crit f`. The hypotheses are exactly those of Theorem 3.1.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1212 (PDF p. 8), Section 3.1, equation (6), recalled from [5, Theorem 13] (Bolte, Daniilidis & Lewis, A Sard theorem for non-differentiable functions, J. Math. Anal. Appl. 321 (2006) 729–740)

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope

open Filter Topology
open scoped ENNReal

namespace NonsmoothLojasiewicz.Continuous

/-- Eq. (6) (p. 1212, recalled from [5, Theorem 13]): for `f` subanalytic with closed domain,
continuous on its domain, and `a ∈ crit f`, the function `f` is constant on the connected
component `(crit f)_a` of `crit f` containing `a`. -/
theorem const_on_crit_component {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : ∀ x, f x ≠ ⊥)
    (hdom : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    (hsub : IsSubanalyticFn f) (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ crit f) :
    ∀ x ∈ connectedComponentIn (crit f) a, f x = f a := by sorry

end NonsmoothLojasiewicz.Continuous
