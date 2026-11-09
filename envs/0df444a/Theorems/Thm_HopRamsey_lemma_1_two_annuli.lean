-- Prove2me | Theorems.Thm_HopRamsey_lemma_1_two_annuli
-- name    : HopRamsey.lemma_1_two_annuli
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:45:17.747431+00:00
-- url     : https://prove2.me/theorems/40bcc124-603a-4228-8725-b1ff80071a5c
-- title:
--   Two-annuli bound: $\Pr[\tau\in\{\rho-1,\rho\}]\le 2p\cdot\Pr[\tau\ge\rho-1]$
-- statement:
--   Let $\tau$ be geometric with parameter $p\in(0,1]$, $\Pr[\tau=R]=(1-p)^Rp$ for $R\ge0$. For every integer $\rho$,
--
--   $$
--   \Pr[\tau\in\{\rho-1,\rho\}]\le 2p\cdot\Pr[\tau\ge\rho-1].
--   $$
--
--   In the proof of Lemma 1 this bounds the probability that a vertex reached by a carved ball stops being padded without joining the ball's padded set by $2p_\ell$ times the probability that the ball reaches it.
--
--   Differences from the source:
--   - generalization: τ_{ℓ,i} geometric with parameter p_ℓ → τ geometric with any parameter p ∈ (0,1]; reason: a fact about the geometric law; p_ℓ ∈ (0,1] under the standing assumptions
--   - encoding: events about an integer-valued τ ≥ 0 and an integer ρ → τ ∈ ℕ compared with ρ ∈ ℤ through the cast ℕ → ℤ; probabilities as PMF outer-measure values; reason: the same events
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), proof of Lemma 1, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_HopRamsey_truncGeom

open scoped ENNReal

namespace HopRamsey

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Two-annuli bound, proof of Lemma 1, p.21 (PDF p.23): "For every fixed integer ρ it holds that
Pr[τ_{ℓ,i} ∈ {ρ−1,ρ}] ≤ 2p_ℓ · Pr[τ_{ℓ,i} ≥ ρ−1] (for ρ ≥ 1 by the calculation above, and for ρ ≤ 0 as
the left hand side is at most Pr[τ_{ℓ,i} = 0] = p_ℓ while the right hand side equals 2p_ℓ)."

**Formalization Note.** `τ` has the geometric law with parameter `p ∈ (0, 1]` on `ℕ`; the events
compare its integer cast with `ρ ∈ ℤ`. -/
theorem lemma_1_two_annuli (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (ρ : ℤ) :
    (geomLaw p).toOuterMeasure {t : ℕ | (t : ℤ) = ρ - 1 ∨ (t : ℤ) = ρ} ≤
      ENNReal.ofReal (2 * p) * (geomLaw p).toOuterMeasure {t : ℕ | ρ - 1 ≤ (t : ℤ)} := by sorry

end HopRamsey
