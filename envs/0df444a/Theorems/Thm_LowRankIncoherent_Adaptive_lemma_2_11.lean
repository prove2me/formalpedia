-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_lemma_2_11
-- name    : LowRankIncoherent.Adaptive.lemma_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:18:59.463732+00:00
-- url     : https://prove2.me/theorems/3223dce5-c8c6-4874-b10c-849627fe9598
-- title:
--   Lemma 2.11 — weighted diamond identities and consequences
-- statement:
--   Fix a channel $E$ of Kraus rank exactly $r$ in the standing feasible dimensions and a positive definite state $σ$. For a state $ρ$ put $L_{ρ,σ}=I_b⊗(\sqrt{ρ^T}(σ^T)^{-1/2})$. Weighted conjugation takes the joint output at $σ$ to the joint output at $ρ$. For every complex joint matrix $M$,
--   $$\operatorname{tr}(L_{ρ,σ}ML_{ρ,σ}^†)=\operatorname{tr}(ρ(\operatorname{tr}_BC_{Φ_σ(M)})^T).$$
--   For Hermitian $M$ the maximum is attained and
--   $$\|Φ_σ(M)\|_⋄=\max_{ρ\text{ a state}}\|L_{ρ,σ}ML_{ρ,σ}^†\|_1.$$
--   For $G\succeq0$ this equals both $\|Φ_σ(G)^†(I_b)\|_∞$ and $\|\operatorname{tr}_BC_{Φ_σ(G)}\|_∞$. If $t≥0$ and $-tG\preceq M\preceq tG$, the diamond norm is at most $t\|\operatorname{tr}_BC_{Φ_σ(G)}\|_∞$. For arbitrary $D\times k$ complex matrices $U,V$,
--   $$\|Φ_σ(UV^†+VU^†)\|_⋄≤2\sqrt{\|\operatorname{tr}_BC_{Φ_σ(UU^†)}\|_∞\,\|\operatorname{tr}_BC_{Φ_σ(VV^†)}\|_∞}.$$
--   These full identities and all three consequences connect matrix order estimates with channel error.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Lemma 2.11, printed p. 14 = PDF p. 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem lemma_2_11 {a b r : ℕ} (ha : 0 < a) (hb : 2 ≤ b) (hrpos : 1 ≤ r)
    (hrmax : r ≤ a*b) (hfeasible : a ≤ r*b) (E : Map a b)
    (hE : E ∈ ChanTomoNB.QChan r a b) (hrank : (choi E).rank = r)
    (σ : Input a) (hσ : State σ) (hpd : σ.PosDef) :
    (∀ ρ, State ρ →
      weightedL ρ σ * outputState E σ * (weightedL ρ σ)ᴴ = outputState E ρ) ∧
    (∀ ρ, State ρ → ∀ M : Joint a b,
      (weightedL ρ σ * M * (weightedL ρ σ)ᴴ).trace =
        (ρ * (ptrB (whiten σ M)).transpose).trace) ∧
    (∀ M : Joint a b, M.IsHermitian →
      ∃ ρ, State ρ ∧
        ChanTomoNB.diamondDist (reconstruct σ M) 0 =
          WildeQIT.traceNorm (weightedL ρ σ * M * (weightedL ρ σ)ᴴ) ∧
        ∀ τ, State τ → WildeQIT.traceNorm (weightedL τ σ * M * (weightedL τ σ)ᴴ) ≤
          ChanTomoNB.diamondDist (reconstruct σ M) 0) ∧
    (∀ G : Joint a b, G.PosSemidef →
      ChanTomoNB.diamondDist (reconstruct σ G) 0 = opNorm (adjointI σ G) ∧
      opNorm (adjointI σ G) = opNorm (ptrB (whiten σ G))) ∧
    (∀ G M : Joint a b, G.PosSemidef → M.IsHermitian → ∀ t : ℝ, 0 ≤ t →
      LE ((-t : ℂ) • G) M → LE M ((t : ℂ) • G) →
      ChanTomoNB.diamondDist (reconstruct σ M) 0 ≤ t * opNorm (ptrB (whiten σ G))) ∧
    (∀ k : ℕ, ∀ U V : Matrix (Fin b × Fin a) (Fin k) ℂ,
      ChanTomoNB.diamondDist (reconstruct σ (U*Vᴴ + V*Uᴴ)) 0 ≤
        2 * Real.sqrt (opNorm (ptrB (whiten σ (U*Uᴴ))) *
          opNorm (ptrB (whiten σ (V*Vᴴ))))) := by sorry

end LowRankIncoherent.Adaptive
