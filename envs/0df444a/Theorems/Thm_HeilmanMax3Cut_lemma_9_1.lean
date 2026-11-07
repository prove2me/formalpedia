-- Prove2me | Theorems.Thm_HeilmanMax3Cut_lemma_9_1
-- name    : HeilmanMax3Cut.lemma_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:03.238335+00:00
-- url     : https://prove2.me/theorems/b3d37849-f04e-4491-9d29-431bad7cce6a
-- title:
--   Lemma 9.1 — spectral bounds
-- statement:
--   Fix $0<\sigma\le1/2$ (the standing assumption of Sections 7–9). Let $\nu$ be the exponential law on $(0,\infty)$, $\langle\cdot,\cdot\rangle$ the inner product of $L^2(\nu)$, $K_*$ the integral operator with kernel $K_*$ (104), $M_{J_*}$ multiplication by $J_*$, and $h_{\mathrm{lower}},h_{\mathrm{upper}}$ the Hilbert–Schmidt quantities (111), (112). Let $z:(0,\infty)\to\mathbb R$ be bounded and measurable.
--
--   1. If $h_{\mathrm{lower}}<\infty$, then $\langle z,K_*z\rangle\ge-h_{\mathrm{lower}}\langle z,M_{J_*}z\rangle$.
--   2. If $h_{\mathrm{upper}}<\infty$ and $\int_0^\infty z\,d\nu=0$, then $\langle z,K_*z\rangle\le h_{\mathrm{upper}}\langle z,M_{J_*}z\rangle$.
--
--   These bounds control the operator part of the quadratic form (132) by its multiplication part.
--
--   Differences from the source:
--   - encoding: z : (0, ∞) → ℝ bounded → z : ℝ → ℝ measurable and bounded on (0, ∞); reason: ν lives on (0, ∞), so values elsewhere are irrelevant; measurability is implicit in the paper, where ⟨z, ·⟩ must be defined
--   - encoding: h_lower, h_upper as real constants in (113), (114) → h ∈ [0, ∞]; each clause assumes h ≠ ∞ and uses its real value; reason: for h = ∞ the inequality has no content
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Lemma 9.1, Eqs. (113)–(114), p.32; standing assumption 0 < σ ≤ 1/2, p.32

import Mathlib
import Definitions.Def_HeilmanMax3Cut_nuExp
import Definitions.Def_HeilmanMax3Cut_Kst
import Definitions.Def_HeilmanMax3Cut_Jst
import Definitions.Def_HeilmanMax3Cut_hLower
import Definitions.Def_HeilmanMax3Cut_hUpper
import Definitions.Def_HeilmanMax3Cut_bil
import Definitions.Def_HeilmanMax3Cut_mulForm
open MeasureTheory

namespace HeilmanMax3Cut

/-- **Lemma 9.1 (Spectral bounds).** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Lemma 9.1, Eqs. (113)–(114), p.32, under the standing
assumption `0 < σ ≤ 1/2` of §§7–9 ("Recall that `0 < σ ≤ 1/2`", p.32): "Let `z : (0, ∞) → ℝ` be
bounded. Then `⟨z, K_* z⟩ ≥ −h_lower ⟨z, M_{J_*} z⟩`. (113) `⟨z, K_* z⟩ ≤ h_upper ⟨z, M_{J_*} z⟩` when
`∫₀^∞ z(s) dν(s) = 0`. (114)"

**Formalization Note.** `⟨·, ·⟩` is the `L²(ν)` inner product (`bil`, `mulForm`). `h_lower`,
`h_upper ∈ [0, ∞]` are lower Lebesgue integrals; each clause is stated when the constant is finite
(for `h = ∞` the paper's inequality has no content), with the real value `toReal`. `z` is
measurable (implicit in the paper, where `⟨z, ·⟩` must make sense) and bounded on `(0, ∞)`. -/
theorem lemma_9_1 (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (z : ℝ → ℝ) (hz : Measurable z)
    (hzb : ∃ C : ℝ, ∀ t ∈ Set.Ioi (0 : ℝ), |z t| ≤ C) :
    (hLower σ ≠ ⊤ → -(hLower σ).toReal * mulForm (Jst σ) z ≤ bil (Kst σ) z z) ∧
    (∫ s, z s ∂nuExp = 0 → hUpper σ ≠ ⊤ →
      bil (Kst σ) z z ≤ (hUpper σ).toReal * mulForm (Jst σ) z) := by sorry

end HeilmanMax3Cut
