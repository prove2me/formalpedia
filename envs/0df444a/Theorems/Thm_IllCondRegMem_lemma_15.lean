-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_15
-- name    : IllCondRegMem.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:06.637134+00:00
-- url     : https://prove2.me/theorems/0f34b846-33ae-41e8-9128-b735c4330fad
-- title:
--   Lemma 15 — properties of the pruning map: $\mathbb P\{\mathrm{FAIL}\}\le p_f$, PRUNED is pruned, witnesses are nearly orthogonal
-- statement:
--   Let $G\subseteq\mathbb R^d$ be a subspace, $D$ a distribution over $\mathrm{Gr}(d_E,G^\perp)$, $p_f>0$ a failure probability, and $(d_0,\delta_{\max})$ pruning parameters with $\delta_{\max}\in(0,1)$ and $d_0\in(d/2,d]$. Let $\Psi=\Psi(\cdot;D,G)$ be the pruning map of §5.1 built with any admissible witness selection rule, and let $E\sim D$. Then:
--
--   1. $\mathbb P\{\Psi(E)=\mathrm{FAIL}\}\le p_f$;
--   2. if $\mathbb P\{\Psi(E)=\mathrm{PRUNED}\}>0$, the conditional law $\mathrm{Law}(E\mid\Psi(E)=\mathrm{PRUNED})$ is $(d_0,\delta_{\max})$-pruned on $G^\perp$;
--   3. if $\Psi(E)=(w,\delta)$ for some $E\in\mathrm{Gr}(d_E,G^\perp)$, then $w\in S^{d-1}\cap G^\perp$, $\delta\in(0,\delta_{\max}]$, and
--   $$
--   \|P_Ew\|<\delta ;
--   $$
--   consequently $G\oplus\mathrm{Span}(P_{E^\perp}w)\subseteq E^\perp$ and this subspace has dimension $\dim G+1$.
--
--   The pruning map either certifies that the remaining posterior is pruned, fails with small probability, or exhibits a direction that enlarges the explored subspace by one dimension; the masked adversary is built on these three properties.
--
--   **Formalization Note** $D$ is the law of a measurable random subspace with values in $\mathrm{Gr}(d_E,G^\perp)$; claim 2 uses `ProbabilityTheory.cond`.
--
--   Differences from the source:
--   - reading: pruning parameters (d₀, δ_max) with no stated range → δ_max ∈ (0,1) and d₀ ∈ (d/2, d]; reason: the ranges of Definition 11 (p.11) are the paper's standing ones; claim 3's dimension count fails for δ_max ≥ 1 (w ∈ E gives P_{E⊥}w = 0)
--   - generalization: the constructed pruning map, with a deterministically selected witness (δ_j within a factor 1/2 of the supremum) → every admissible selection rule, a function of the current region; reason: the lemma holds for each such deterministic choice; the paper's map is one of them
--   - encoding: distribution D over Gr(d_E, G⊥); E ∼ D; Law(E | ·) → law of a measurable random subspace E with values in Gr(d_E, G⊥); ProbabilityTheory.cond; reason: Lean representation of a distribution on subspaces; same probabilities
--   - encoding: codomain {FAIL, PRUNED} ∪ (S^{d−1} ∩ G⊥) × (0, δ_max] of Ψ → stated in claim 3 as ‖w‖ = 1, w ∈ G⊥, 0 < δ ≤ δ_max; reason: the codomain is part of the statement; Lean's output type does not carry it
--   - encoding: R₀ = Gr(d_E, G⊥) → R₀ = all subspaces; reason: D is supported on Gr(d_E, G⊥), so every D-mass is the same
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 15, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_IllCondRegMem_pruningMap

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- **Lemma 15 (Pruning properties).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 15,
p.20: "Fix a subspace G ⊂ ℝ^d, a distribution D over Gr(d_E, G⊥), a fixed failure probability
p_f > 0 and pruning parameters (d₀, δ_max). The constructed pruning map
Ψ(·; D, G) : Gr(d_E, G⊥) → {FAIL, PRUNED} ∪ (S^{d−1} ∩ G⊥) × (0, δ_max] has the following
properties for E ∼ D. 1. P{Ψ(E; D, G) = FAIL} ≤ p_f. 2. If P[Ψ(E; D, G) = PRUNED] > 0, then the
conditional distribution on the PRUNED state Law(E | Ψ(E; D, G) = PRUNED) is (d₀, δ_max)-pruned
on G⊥. 3. If Ψ(E; D, G) = (w, δ), then ‖P_E w‖ < δ. So G ⊕ Span(P_{E⊥} w) ⊆ E⊥ has dimension
dim G + 1."

**Formalization Note.** `D` is the law of a measurable random subspace `E` with values in
`Gr(d_E, G⊥)`; the pruning parameters have the ranges of Definition 11 (p.11),
`δ_max ∈ (0, 1)` and `d₀ ∈ (d/2, d]`. The statement holds for every admissible witness selection
rule (`IsSelectionRule`). The codomain of `Ψ` is part of claim 3: a returned pair has
`w ∈ S^{d−1} ∩ G⊥` and `δ ∈ (0, δ_max]`. Claim 2 uses `ProbabilityTheory.cond`. Claim 3 is
stated for every `E′ ∈ Gr(d_E, G⊥)`. -/
theorem lemma_15 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Ω → Submodule ℝ (Vec d)) (G : Submodule ℝ (Vec d)) (dE d₀ : ℕ) (pf δmax : ℝ)
    (rule : Set (Submodule ℝ (Vec d)) → Vec d × ℝ)
    (hE : IsRandomSubspace E) (hEG : ∀ ω, Module.finrank ℝ (E ω) = dE ∧ E ω ≤ Gᗮ)
    (hpf : 0 < pf) (hδ0 : 0 < δmax) (hδ1 : δmax < 1) (hd₀ : d < 2 * d₀) (hd₀' : d₀ ≤ d)
    (hrule : IsSelectionRule P E G pf d₀ δmax rule) :
    P {ω | pruningMap P E G pf d₀ δmax rule (E ω) = PruneOut.fail} ≤ ENNReal.ofReal pf ∧
    (0 < P {ω | pruningMap P E G pf d₀ δmax rule (E ω) = PruneOut.pruned} →
      IsPrunedOn (cond P {ω | pruningMap P E G pf d₀ δmax rule (E ω) = PruneOut.pruned})
        E G d₀ δmax) ∧
    ∀ (E' : Submodule ℝ (Vec d)) (w : Vec d) (δ : ℝ),
      Module.finrank ℝ E' = dE → E' ≤ Gᗮ →
      pruningMap P E G pf d₀ δmax rule E' = PruneOut.witness w δ →
        (‖w‖ = 1 ∧ w ∈ Gᗮ ∧ 0 < δ ∧ δ ≤ δmax) ∧ ‖E'.starProjection w‖ < δ ∧
        G ⊔ Submodule.span ℝ {E'ᗮ.starProjection w} ≤ E'ᗮ ∧
        Module.finrank ℝ (G ⊔ Submodule.span ℝ {E'ᗮ.starProjection w} : Submodule ℝ (Vec d)) =
          Module.finrank ℝ G + 1 := by sorry

end IllCondRegMem
