-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Deterministic_resolvent_norm
-- name    : NearlyUnstableHawkes.Deterministic.resolvent_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:13.596921+00:00
-- url     : https://prove2.me/theorems/d106c539-6508-4b72-a3f9-6ba405028fbe
-- title:
--   §4.1, p. 14 — L¹ mass of the Hawkes resolvent
-- statement:
--   If $\phi^T=a\phi$ with $0<a<1$ and $\int_0^\infty\phi(s)\,ds=1$, then its nonnegative resolvent $\psi^T=\sum_{k\ge1}(\phi^T)^{*k}$ has mass
--
--   $$\|\psi^T\|_1=\frac{\|\phi^T\|_1}{1-\|\phi^T\|_1}=\frac{a}{1-a}.$$
--
--   This identity gives the exact cancellation of the near-instability factor in the pathwise estimate.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 14, §4.1, “Thus, using that” display

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

namespace NearlyUnstableHawkes.Deterministic

/-- Jaisson–Rosenbaum, §4.1, p. 14, resolvent mass display. -/
theorem resolvent_norm (a m : ℝ) (φ φ' : ℝ → ℝ)
    (ha0 : 0 < a) (ha1 : a < 1)
    (hφ : KernelAssumption φ φ' m) :
    psiNorm (scaledKernel a φ) = a / (1 - a) := by sorry

end NearlyUnstableHawkes.Deterministic
