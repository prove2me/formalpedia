-- Prove2me | Theorems.Thm_MartOT_Curtain_lemma_5_2
-- name    : MartOT.Curtain.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:29.463711+00:00
-- url     : https://prove2.me/theorems/e7ece882-0528-4239-a3a6-dacd66679d36
-- title:
--   Lemma 5.2, p. 33 — a nonzero signed measure of mass 0 has ∫ g_{a,b} dσ > 0 for some a ∈ spt σ⁺ and b > a
-- statement:
--   Let $\sigma$ be a nonzero finite signed Borel measure on $\mathbb R$ with total mass $\sigma(\mathbb R)=0$, and let $\sigma=\sigma^+-\sigma^-$ be its Hahn–Jordan decomposition, with $\sigma^+\perp\sigma^-$. With the functions $g_{u,v}$ of (13), there exist $a\in\operatorname{spt}(\sigma^+)$ and $b>a$ such that
--
--   $$\int g_{a,b}(x)\,d\sigma(x)>0 .$$
--
--   The lemma gives a test function, anchored at a point of the support of the positive part, that detects $\sigma\neq0$. In the uniqueness proof of the left-curtain coupling it is applied to $\sigma=\nu^{\pi_{\mathrm{lc}}}_x-\nu^{\pi}_x$.
--
--   **Formalization Note** The signed measure is given by its Jordan parts: two finite measures $\sigma^+,\sigma^-$ that are mutually singular, of equal total mass (mass of $\sigma$ is $0$), and distinct ($\sigma\neq0$); this pair is exactly the Hahn–Jordan decomposition of $\sigma=\sigma^+-\sigma^-$. $\int g\,d\sigma$ is $\int g\,d\sigma^+-\int g\,d\sigma^-$ (both finite: $g_{a,b}$ is bounded Borel). The support is Mathlib's `Measure.support`.
-- source:
--   arXiv:1208.1509v2, Lemma 5.2 and display (13), p. 33

import Mathlib
import Definitions.Def_MartOT_Curtain_gUV

namespace MartOT.Curtain

open MeasureTheory

theorem lemma_5_2 (σp σm : Measure ℝ) [IsFiniteMeasure σp] [IsFiniteMeasure σm]
    (hsing : σp ⟂ₘ σm) (hmass : σp Set.univ = σm Set.univ) (hne : σp ≠ σm) :
    ∃ a ∈ σp.support, ∃ b : ℝ, a < b ∧
      0 < (∫ x, gUV a b x ∂σp) - ∫ x, gUV a b x ∂σm := by sorry

end MartOT.Curtain
