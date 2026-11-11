-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_lemma_F_5
-- name    : OrderSelProphet.Kernel.lemma_F_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:59:39.642208+00:00
-- url     : https://prove2.me/theorems/5fff7f72-2ab0-44dd-88d5-25259d3011d8
-- title:
--   Lemma F.5 — finite numerical certificate (assembled): $\bar\ell_\lambda\le U_{\max}$ for every profile with nonzero mass vector, and $U_{\max}<U_{\rm cert}<1$
-- statement:
--   The supplementary regional certificate for $(K_1,\Gamma_1)$ covers $[0,1]^4\setminus\{0\}$ and gives $\sup_{\lambda\in\Lambda(\mathcal R)}\bar\ell_\lambda\le U(\mathcal R)$ on every region of the cover; the largest assembled endpoint is
--   $$U_{\max}=\frac{9007199253707871}{9007199254740992}<U_{\rm cert}<1.\quad(131)$$
--   Stated as the bound it assembles: for every profile $\lambda$ whose mass vector $x(\lambda)$ is not $0$, $\bar\ell_\lambda\le U_{\max}$; and $U_{\max}<U_{\rm cert}<1$.
--
--   Differences from the source:
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - reading: sup over Λ(R) of ℓ̄_λ ≤ U(R) on every region R of a cover of [0,1]⁴ \ {0} given in the external package order_selection_074500001_certificate_final.zip, and Umax = the largest U(R) → for every profile λ with x(λ) ≠ 0, auxLoad λ ≤ Umax; Umax < Ucert < 1; reason: the regions are not in the PDF; this is exactly how the lemma is used in the proof of Theorem 6.1 (p. 57), and every mass vector lies in [0,1]⁴
--   - encoding: ℓ̄_λ (real) → auxLoad λ in ℝ≥0∞; reason: nonnegative load
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Lemma F.5, p. 57

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Certificate

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Lemma F.5 (Finite numerical certificate), p. 57, as the bound it assembles: every profile
with a nonzero mass vector has auxiliary load at most `Umax`, and `Umax < Ucert < 1`. -/
theorem lemma_F_5 :
    (∀ lam : Profile, (∃ g, massVec lam.1 g ≠ 0) → auxLoad lam.1 ≤ ENNReal.ofReal Umax) ∧
      Umax < Ucert ∧ Ucert < 1 := by sorry

end OrderSelProphet.Kernel
