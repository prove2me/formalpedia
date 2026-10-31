-- Prove2me | Theorems.Thm_ImpliedAmbiguity_lemma_4_S_eq_Sigma
-- name    : ImpliedAmbiguity.lemma_4_S_eq_Sigma
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:06:49.168833+00:00
-- url     : https://prove2.me/theorems/20af1deb-d793-4640-b462-07fbc2056974
-- title:
--   Lemma 4 with $S=\Sigma$ — the minimizer and minimum of $\eta^\theta$ in rewritten form
-- statement:
--   Let $x, c\in\mathbb R^N$ and let $\Sigma$ be a symmetric positive definite $N\times N$ matrix. Put $v^\theta = \theta^{-1}\Sigma^{-1}c - x$, assume $v^\theta\neq 0$ for every $\theta>0$ and $x\cdot c>0$, and write $\bar\theta = (x^\top\Sigma x)^{-1}(x\cdot c)$ and $w = \bar\theta^{-1}c - \Sigma x$. Let $\eta^\theta = (v^\theta)^\top\Sigma v^\theta / x^\top\Sigma v^\theta$ (the function (32) of Lemma 4 with $S = \Sigma$), and let $\theta^*$ be given by
--
--   $$
--   \frac1{\theta^*} = \frac1{\bar\theta} + \left(\frac{w^\top\Sigma^{-1}w}{c^\top\Sigma^{-1}c}\right)^{1/2}.
--   $$
--
--   Then $\eta^\theta > 0$ on $(0,\bar\theta)$, $\theta^*\in(0,\bar\theta)$, $\theta^*$ is the unique minimizer of $\eta^\theta$ on $(0,\bar\theta)$, and
--
--   $$
--   \eta^{\theta^*} = \frac{2}{x\cdot c}\left(\Bigl(\bigl(c^\top\Sigma^{-1}c\bigr)\, w^\top\Sigma^{-1}w\Bigr)^{1/2} + w^\top\Sigma^{-1}c\right).
--   $$
--
--   These are the two displays by which the paper rewrites (33) and (34) for $S = \Sigma$, in terms of the data $c$, $\Sigma$, $x$ only; the proof of Theorem 4 starts from them.
--
--   Differences from the source:
--   - reading: "To find the minimum of η^θ over θ ∈ (0, θ̄), we take S = Σ. Then (33) can be rewritten as … and (34) can be rewritten as …" → Lemma 4's conclusion at S = Σ with the two displays as minimizer and minimum; reason: the displays are the rewritten (33) and (34), which Lemma 4 asserts are the minimizer and the minimum.
--   - encoding: θ̄, v^θ, η^θ, (·)^{1/2}, S^N_++ → `thetaBar`, `vTheta`, `etaTheta` (total in θ, minimized over `Set.Ioo 0 θ̄`), `Real.sqrt`, `Matrix.PosDef`; reason: Lean convention; same instances.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), Appendix C, displays after Lemma 4, p.41

import Mathlib
import Definitions.Def_ImpliedAmbiguity_thetaBar
import Definitions.Def_ImpliedAmbiguity_vTheta
import Definitions.Def_ImpliedAmbiguity_etaTheta

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
Appendix C, display after Lemma 4, p.41: "To ﬁnd the minimum of η^θ over θ ∈ (0, θ̄), we take
S = Σ. Then (33) can be rewritten as
`1/θ = 1/θ̄ + ((θ̄⁻¹c − Σx)ᵀΣ⁻¹(θ̄⁻¹c − Σx) / cᵀΣ⁻¹c)^{1/2}`, and (34) can be rewritten as
`(2/x·c)(((cᵀΣ⁻¹c)(θ̄⁻¹c − Σx)ᵀΣ⁻¹(θ̄⁻¹c − Σx))^{1/2} + (θ̄⁻¹c − Σx)ᵀΣ⁻¹c)`."

Stated as Lemma 4's conclusion for `S = Σ`, with (33) and (34) in this rewritten form: under
Lemma 4's hypotheses, `η^θ = (v^θ)ᵀΣv^θ / xᵀΣv^θ` is positive on `(0, θ̄)`, the `θ` of the first
display lies in `(0, θ̄)` and is the unique minimizer of `η^θ` there, and the minimum is the
second display.

**Formalization Note.** `Σ` is named `Sig`; `x · c` is `x ⬝ᵥ c`; `θ̄` is `thetaBar Sig c x`;
`η^θ` is `etaTheta Sig c x θ` (the function (32) with `S = Σ`); `(·)^{1/2}` is `Real.sqrt`. -/
theorem lemma_4_S_eq_Sigma {N : ℕ} (x c : Fin N → ℝ) (Sig : Matrix (Fin N) (Fin N) ℝ)
    (hSig : Sig.PosDef)
    (hv : ∀ θ : ℝ, 0 < θ → vTheta Sig c x θ ≠ 0)
    (hxc : 0 < x ⬝ᵥ c) :
    let θbar := thetaBar Sig c x
    let w := θbar⁻¹ • c - Sig *ᵥ x
    let θstar := (1 / θbar + Real.sqrt ((w ⬝ᵥ (Sig⁻¹ *ᵥ w)) / (c ⬝ᵥ (Sig⁻¹ *ᵥ c))))⁻¹
    (∀ θ ∈ Set.Ioo 0 θbar, 0 < etaTheta Sig c x θ) ∧
    θstar ∈ Set.Ioo 0 θbar ∧
    IsMinOn (etaTheta Sig c x) (Set.Ioo 0 θbar) θstar ∧
    (∀ θ ∈ Set.Ioo 0 θbar, etaTheta Sig c x θ = etaTheta Sig c x θstar → θ = θstar) ∧
    etaTheta Sig c x θstar = 2 / (x ⬝ᵥ c) *
      (Real.sqrt ((c ⬝ᵥ (Sig⁻¹ *ᵥ c)) * (w ⬝ᵥ (Sig⁻¹ *ᵥ w))) + w ⬝ᵥ (Sig⁻¹ *ᵥ c)) := by sorry

end ImpliedAmbiguity
