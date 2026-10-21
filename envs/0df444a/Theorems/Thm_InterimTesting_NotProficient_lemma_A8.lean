-- Prove2me | Theorems.Thm_InterimTesting_NotProficient_lemma_A8
-- name    : InterimTesting.NotProficient.lemma_A8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:38.361437+00:00
-- url     : https://prove2.me/theorems/3ce957a5-bfc9-4d5e-85f6-fc0056acb12d
-- title:
--   Lemma A8 (S0 = N), p. A17 (PDF 43) — for B = 0, first-period effort is 1 iff π ≥ 1/(µ(1−µ)A²)
-- statement:
--   Suppose the baseline proficiency factor is $B=0$ (condition (14) is not assumed) and the school starts the year not proficient. Under either assessment decision and for every incentive $\pi\ge0$, the teachers' optimal first-period effort is
--   $$\tilde e_0^*(N)=\begin{cases}0,&\pi<\tilde{\mathcal T}_0(N),\\1,&\tilde{\mathcal T}_0(N)\le\pi,\end{cases}\qquad \tilde{\mathcal T}_0(N)=\frac{1}{\mu(1-\mu)A^2}.$$
--
--   With $B=0$ the first-period threshold does not depend on the accuracy of the midyear information.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), p. A17 (PDF 43), Lemma A8, (A103), (A105)

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

namespace InterimTesting.NotProficient

/-- Lemma A8, `S0 = N` part, p. A17: if `B = 0` (without (14)), the optimal first-period effort
is `1` if `π ≥ 𝒯̃0(N) = 1 / (μ (1 − μ) A²)` and `0` otherwise, with or without the interim
assessment. -/
theorem lemma_A8 (θ : Params) (hθ : θ.Standing) (hB : θ.B = 0) (zI : Bool) (π : ℝ)
    (hπ : 0 ≤ π) :
    e0Star θ zI .N π = if 1 / (θ.μ * (1 - θ.μ) * θ.A ^ 2) ≤ π then 1 else 0 := by sorry

end InterimTesting.NotProficient
