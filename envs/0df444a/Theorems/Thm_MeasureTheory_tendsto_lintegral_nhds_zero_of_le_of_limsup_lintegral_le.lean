-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le
-- name    : MeasureTheory.tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/efeab0d2-8fc7-5218-8cc8-1bacacf00792
-- title:
--   Pratt's lemma for lower integrals with moving dominators
-- statement:
--   Let $\alpha$ and $\iota$ be types, $\alpha$ equipped with a measurable space structure, $\mu$ a measure on $\alpha$, and $l$ a countably generated filter on $\iota$. Let $F, G \colon \iota \to \alpha \to [0,\infty]$ and $g \colon \alpha \to [0,\infty]$ be given, and assume: each $F_i$ and each $G_i$ is almost everywhere measurable with respect to $\mu$; for each $i$ one has $F_i(x) \le G_i(x)$ for $\mu$-almost every $x$; for $\mu$-almost every $x$ the net $i \mapsto F_i(x)$ tends to $0$ along $l$; for $\mu$-almost every $x$ the net $i \mapsto G_i(x)$ tends to $g(x)$ along $l$; the lower Lebesgue integral $\int^- g \, d\mu$ is not $\infty$; and $\limsup_{l} \int^- G_i \, d\mu \le \int^- g \, d\mu$. The conclusion is that $i \mapsto \int^- F_i \, d\mu$ tends to $0$ along $l$, the limit being taken in the order topology of $[0,\infty]$. All integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions, so no integrability hypothesis beyond finiteness of $\int^- g$ is imposed.
--
--   This is the generalised dominated convergence theorem, also known as Pratt's lemma, in the form with a varying dominating family $G_i \to g$ and with the dominated family tending to $0$, stated for filters rather than sequences. It is used in the construction of the cuspidal spectrum, for [`AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt), i.e. for continuity of right translation in the $L^2$-norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le.lean

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter
open scoped ENNReal Topology

theorem MeasureTheory.tendsto_lintegral_nhds_zero_of_le_of_limsup_lintegral_le
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F G : ι → α → ℝ≥0∞) (g : α → ℝ≥0∞)
    (hF : ∀ i, AEMeasurable (F i) μ) (hG : ∀ i, AEMeasurable (G i) μ)
    (hFG : ∀ i, ∀ᵐ x ∂μ, F i x ≤ G i x)
    (hF0 : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 0))
    (hGg : ∀ᵐ x ∂μ, Tendsto (fun i => G i x) l (𝓝 (g x)))
    (hg : ∫⁻ x, g x ∂μ ≠ ∞)
    (hlim : limsup (fun i => ∫⁻ x, G i x ∂μ) l ≤ ∫⁻ x, g x ∂μ) :
    Tendsto (fun i => ∫⁻ x, F i x ∂μ) l (𝓝 0) := by sorry
