-- Prove2me | Theorems.Thm_KingmanSubadditive_BanachAlgebra_truncation_isSubadditive
-- name    : KingmanSubadditive.BanachAlgebra.truncation_isSubadditive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:49.730149+00:00
-- url     : https://prove2.me/theorems/06ebeeef-e62e-462d-9b72-584544ff2460
-- title:
--   Proof of Theorem 2, p. 886 — x_st^(N) = max(x_st, −N(t − s)) is a subadditive process
-- statement:
--   Let $x=(x_{st})_{s<t}$ be a family of real random variables satisfying conditions S₁, S₂ and S₃′ of Kingman's §1.1–1.2, and let $N$ be a positive integer. Define
--   $$x^{(N)}_{st}=\max\big(x_{st},\,-N(t-s)\big),\qquad s<t.$$
--   Then $x^{(N)}$ is a **subadditive process**: it satisfies S₁, S₂ and S₃ (each $x^{(N)}_{0t}$, $t\ge1$, is integrable and $E(x^{(N)}_{0t})\ge -At$ for some constant $A$).
--
--   This is the first step of the proof of Theorem 2: truncating from below restores condition S₃, so that Kingman's ergodic theorem (Theorem 1) applies to each $x^{(N)}$.
--
--   **Formalization Note** "Subadditive process" means: every $x^{(N)}_{st}$ measurable, S₁ almost surely for each triple, S₂ as equality of the laws of the whole shifted and unshifted paths, and S₃.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 886, §1.2, proof of Theorem 2

import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

/-- **Proof of Theorem 2, §1.2, p. 886** (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), DOI 10.1214/aop/1176996798). "It is trivial to check that `x^(N)` is a
subadditive process, where `x_st^(N) = max(x_st, −N(t − s))` and `N` is any positive integer."
The hypotheses are those of Theorem 2 that the truncation uses: `x` is a measurable family of real
random variables satisfying S₁, S₂ and S₃′.

**Formalization Note.** "Subadditive process" is `IsSubadditiveProcess`: measurability, S₁
(almost surely, for each triple), S₂ (joint-law stationarity of the whole path) and S₃
(integrable `x_0t^(N)` with a linear lower bound on the means). -/
theorem truncation_isSubadditive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hmeas : IsMeasurableFamily x) (h1 : S1 P x) (h2 : S2 P x) (h3' : S3' P x)
    (N : ℕ) (hN : 1 ≤ N) :
    IsSubadditiveProcess P (truncate x N) := by sorry

end KingmanSubadditive.BanachAlgebra
