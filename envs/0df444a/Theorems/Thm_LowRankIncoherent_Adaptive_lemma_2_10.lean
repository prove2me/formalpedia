-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_lemma_2_10
-- name    : LowRankIncoherent.Adaptive.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:22.477491+00:00
-- url     : https://prove2.me/theorems/d8d58d78-6f7f-4d77-a2b6-b11eeb408ad7
-- title:
--   Lemma 2.10 — Haar outcomes and snapshot moments
-- statement:
--   Let $X$ be a state on $ℂ^d$, $d≥1$, and let $n≥1$ independent Haar/Born experiments give snapshots $Y$ and their mean $\widehat X_n$. The observed vector has density $p_X(v)=d⟨v|X|v⟩$, with $0≤p_X(v)≤d$ on the unit sphere. With unhalved trace and Euclidean spectral norm,
--   $$\mathbb EY=X,\quad \mathbb EY^2=(d-1)X+dI,\quad \mathbb E(Y-X)^2\preceq2dI,\quad \|Y-X\|_∞≤d+1.$$
--   There is an absolute $c_H>0$, before all parameters, such that for every $0<ζ<1$,
--   $$\Pr\!\left\{\|\widehat X_n-X\|_∞>c_H\left(\sqrt{\frac{d+\log(2/ζ)}n}+\frac{d+\log(2/ζ)}n\right)\right\}≤ζ.$$
--   Every unitary preserving $X$ also preserves the law of the estimator under conjugation. The statement includes probability normalization, estimator measurability, and integrability of the three moment expressions. These establish the actual experiment's moment and concentration interfaces.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Lemma 2.10, printed p. 12 = PDF p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal Matrix.Norms.L2Operator
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem lemma_2_10 : ∃ cH : ℝ, 0 < cH ∧
    ∀ (d n : ℕ) (hd : 0 < d), 1 ≤ n → ∀ X : Input d, State X →
    let μ := experimentLaw X
    let p := fun v : Fin d → ℂ => (d : ℝ) * (∑ i, ∑ j, star (v i) * X i j * v j).re
    let sphere := (basisLaw (Fin d)).map (fun U => column U ⟨0,hd⟩)
    IsProbabilityMeasure μ ∧ IsProbabilityMeasure (batchLaw X n) ∧
    Measurable (estimate (ι := Fin d) (n := n)) ∧
    μ.map observed = sphere.withDensity (fun v => ENNReal.ofReal (p v)) ∧
    (∀ v : Fin d → ℂ, (∑ i, ‖v i‖^2) = 1 → 0 ≤ p v ∧ p v ≤ d) ∧
    Integrable snapshot μ ∧ Integrable (fun z => snapshot z * snapshot z) μ ∧
    Integrable (fun z => (snapshot z-X)*(snapshot z-X)) μ ∧
    (∫ z, snapshot z ∂μ) = X ∧
    (∫ z, snapshot z * snapshot z ∂μ) = ((d : ℂ)-1) • X + (d : ℂ) • 1 ∧
    LE (∫ z, (snapshot z-X)*(snapshot z-X) ∂μ) ((2*d : ℕ) • (1 : Input d)) ∧
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ i : Fin d,
      opNorm (snapshot ((U : Input d),(Fintype.equivFin (Fin d)) i)-X) ≤ d+1) ∧
    (∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      (batchLaw X n) {z | opNorm (estimate z-X) >
        cH*(Real.sqrt ((d+Real.log (2/ζ))/n) + (d+Real.log (2/ζ))/n)} ≤ ENNReal.ofReal ζ) ∧
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      (U : Input d)*X*(U : Input d)ᴴ = X →
      (batchLaw X n).map (fun z => (U : Input d)*estimate z*(U : Input d)ᴴ) =
        (batchLaw X n).map estimate) := by sorry

end LowRankIncoherent.Adaptive
