-- Prove2me | Theorems.Thm_NovyPQZK_Main_lemma_3
-- name    : NovyPQZK.Main.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:35:53.817165+00:00
-- url     : https://prove2.me/theorems/33351fa3-d9af-4a73-9bc4-f10f8b9ccefc
-- title:
--   Lemma 3 — Watrous single-reflection lands close to the success state
-- statement:
--   Let $\Delta = \{\Delta_1,\Delta_0\}$ be a projective measurement and $\Gamma$ a projector on a finite-dimensional register. For every unit vector $|\psi\rangle$ with $\Gamma|\psi\rangle = |\psi\rangle$ and $\|\Delta_1|\psi\rangle\|>0$, put $|\mathrm{Success}\rangle = \Delta_1|\psi\rangle/\|\Delta_1|\psi\rangle\|$. Then
--
--   $$F^2\big(\mathrm{WatRefl}^\Gamma_\Delta(|\psi\rangle\langle\psi|),\ |\mathrm{Success}\rangle\langle\mathrm{Success}|\big)\ \ge\ 4\,\|(1-\Gamma)\Delta_1|\psi\rangle\|^2 .$$
--
--   Since $\|(1-\Gamma)\Delta_1|\psi\rangle\|^2\le 1/4$, the bound is close to $1$ exactly when the success probability is close to $1/2$ and $\Delta_1|\psi\rangle$ lies halfway in the image of $\Gamma$; this is how the inverter's searcher rewinds one round.
--
--   Differences from the source:
--   - encoding: state |ψ⟩, projective measurement Δ = {Δ₁, Δ₀}, norm ‖·‖ → unit vector ψ : ι → ℂ, IsTwoOutcomeMeas Δ₁ Δ₀ (projectors with Δ₁ + Δ₀ = 1), ‖v‖² = Σ|vᵢ|², |Success⟩ written out; reason: finite-dimensional registers as on p. 14
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3.2 p. 18, Lemma 3

import Mathlib
import Definitions.Def_NovyPQZK_Main_Fidelity
import Definitions.Def_NovyPQZK_Main_WatRefl

namespace NovyPQZK.Main

theorem lemma_3 {ι : Type} [Fintype ι] [DecidableEq ι] (Δ₁ Δ₀ Γ : Matrix ι ι ℂ)
    (hΔ : IsTwoOutcomeMeas Δ₁ Δ₀) (hΓ : IsProjector Γ) (ψ : ι → ℂ)
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) (hΓψ : Γ.mulVec ψ = ψ)
    (hpos : 0 < ∑ i, ‖(Δ₁.mulVec ψ) i‖ ^ 2) :
    fidelity (watRefl Γ Δ₁ Δ₀ (pureDM ψ))
        (pureDM fun i => (Δ₁.mulVec ψ) i / ((Real.sqrt (∑ j, ‖(Δ₁.mulVec ψ) j‖ ^ 2) : ℝ) : ℂ)) ^ 2 ≥
      4 * ∑ i, ‖((1 - Γ).mulVec (Δ₁.mulVec ψ)) i‖ ^ 2 := by sorry

end NovyPQZK.Main
