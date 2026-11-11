-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_lemma_2_6
-- name    : LogConcaveLattice.Lift.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:52.149025+00:00
-- url     : https://prove2.me/theorems/50c6c696-3b09-4eb0-bd88-3f15e2428f56
-- title:
--   Lemma 2.6 — $X+\Lambda$ is uniform on $\mathbb R^n/\Lambda$ iff $\sum_{\lambda}p(x+\lambda)=1/\det\Lambda$ a.e.
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice and let $X$ have probability density $p$ on $\mathbb R^n$ ($p$ measurable, $p\ge0$, $\int p=1$). Then $X+\Lambda$ is uniformly distributed on $\mathbb R^n/\Lambda$ if and only if
--   $$\sum_{\lambda\in\Lambda}p(x+\lambda)=\frac1{\det\Lambda}\qquad\text{for almost every }x\in\mathbb R^n .$$
--
--   This is the criterion by which the proof of Theorem 1.1 checks that its densities are uniform modulo the lattice, and by which the converse extracts a pointwise bound from uniformity.
--
--   Differences from the source:
--   - encoding: "X + Λ is uniformly distributed on Rⁿ/Λ" → the push-forward of the law p·Lebesgue under x ↦ x + Λ equals the uniform measure (law of U + Λ, U uniform on a fundamental parallelepiped), on the quotient σ-algebra; reason: the definition of p. 8; same instances
--   - encoding: the lattice sum as a real number → the sum of ENNReal.ofReal (p (x + λ)) in [0, ∞], compared with 1/det Λ; reason: for an integrable p the sum is finite a.e., while a real tsum would read a divergent sum as 0; same instances
--   - encoding: probability density p → measurable p ≥ 0 with lower Lebesgue integral 1; det Λ → ZLattice.covolume Λ; reason: standard meaning; same instances
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, Lemma 2.6, p. 9 (uniform measure on R^n/Λ: §2.5, p. 8)

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_UniformQuotient

open MeasureTheory

namespace LogConcaveLattice.Lift

/-- **Lemma 2.6** (p. 9): let `Λ ⊆ ℝⁿ` be a full-rank lattice and let `X` have probability
density `p` on `ℝⁿ`. Then `X + Λ` is uniformly distributed on `ℝⁿ/Λ` if and only if
`∑_{λ∈Λ} p(x + λ) = 1 / det Λ` for almost every `x ∈ ℝⁿ` (the lattice sum read in `[0, ∞]`). -/
theorem lemma_2_6 (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (p : V n → ℝ) (hp_meas : Measurable p) (hp_nonneg : ∀ x, 0 ≤ p x)
    (hp_one : ∫⁻ x, ENNReal.ofReal (p x) = 1) :
    Measure.map (QuotientAddGroup.mk : V n → V n ⧸ Λ.toAddSubgroup)
        (volume.withDensity fun x => ENNReal.ofReal (p x)) = uniformQuot Λ ↔
      ∀ᵐ x : V n, ∑' l : Λ, ENNReal.ofReal (p (x + l)) = ENNReal.ofReal (1 / ZLattice.covolume Λ) := by sorry

end LogConcaveLattice.Lift
