-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_16
-- name    : IllCondRegMem.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:50.932039+00:00
-- url     : https://prove2.me/theorems/614ff912-9ab4-4802-b3c3-075b19da3ace
-- title:
--   Lemma 16 — replay lemma: $\mathbb P\{\Psi(E';D,G)=(w,\delta)\}\ge p_f\delta^{d_0}$
-- statement:
--   In the setting of Lemma 15 ($G$, $D$ over $\mathrm{Gr}(d_E,G^\perp)$, $p_f>0$, $\delta_{\max}\in(0,1)$, $d_0\in(d/2,d]$, any admissible witness selection rule), let $(w,\delta)$ be in the image of $\Psi(\cdot;D,G)$ on $\mathrm{Gr}(d_E,G^\perp)$. Then an independent proxy $E'\sim D$ satisfies
--   $$
--   \mathbb P\{\Psi(E';D,G)=(w,\delta)\}\ge p_f\,\delta^{d_0}.
--   $$
--   Any pair the pruning map can output is reproduced with non-negligible probability by an independent run; the reduction to the orthogonal vector game uses this to simulate the masked adversary.
--
--   **Formalization Note** The proxy $E'$ is the random subspace whose law is $D$.
--
--   Differences from the source:
--   - reading: pruning parameters (d₀, δ_max) with no stated range → δ_max ∈ (0,1) and d₀ ∈ (d/2, d]; reason: the ranges of Definition 11 (p.11), as in Lemma 15
--   - generalization: the constructed pruning map → every admissible selection rule; reason: the lemma holds for each deterministic witness choice; the paper's map is one of them
--   - encoding: E′ ∼ D, image(Ψ(·; D, G)) → the random subspace with law D; image over Gr(d_E, G⊥); reason: Lean representation
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 16, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_IllCondRegMem_pruningMap

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- **Lemma 16 (Replay lemma).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 16,
p.21: "Let (w, δ) ∈ image(Ψ(·; D, G)). An independent proxy E′ ∼ D satisfies
P{Ψ(E′; D, G) = (w, δ)} ≥ p_f δ^{d₀}."

**Formalization Note.** Same setting as Lemma 15: `D` is the law of a measurable random subspace
`E` with values in `Gr(d_E, G⊥)`, `p_f > 0`, `δ_max ∈ (0, 1)`, `d₀ ∈ (d/2, d]` (Definition 11,
p.11), and any admissible witness selection rule. The image is over `Gr(d_E, G⊥)`, the domain of
`Ψ`; the proxy `E′ ∼ D` is the random subspace `E` itself. -/
theorem lemma_16 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Ω → Submodule ℝ (Vec d)) (G : Submodule ℝ (Vec d)) (dE d₀ : ℕ) (pf δmax : ℝ)
    (rule : Set (Submodule ℝ (Vec d)) → Vec d × ℝ)
    (hE : IsRandomSubspace E) (hEG : ∀ ω, Module.finrank ℝ (E ω) = dE ∧ E ω ≤ Gᗮ)
    (hpf : 0 < pf) (hδ0 : 0 < δmax) (hδ1 : δmax < 1) (hd₀ : d < 2 * d₀) (hd₀' : d₀ ≤ d)
    (hrule : IsSelectionRule P E G pf d₀ δmax rule) (w : Vec d) (δ : ℝ)
    (himg : ∃ E' : Submodule ℝ (Vec d), Module.finrank ℝ E' = dE ∧ E' ≤ Gᗮ ∧
      pruningMap P E G pf d₀ δmax rule E' = PruneOut.witness w δ) :
    ENNReal.ofReal (pf * δ ^ d₀) ≤
      P {ω | pruningMap P E G pf d₀ δmax rule (E ω) = PruneOut.witness w δ} := by sorry

end IllCondRegMem
