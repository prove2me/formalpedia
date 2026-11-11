-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_lemma_2_5
-- name    : LogConcaveLattice.Lift.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:35.680571+00:00
-- url     : https://prove2.me/theorems/27ca3670-dfbd-45da-9039-ec0440754191
-- title:
--   Lemma 2.5 — two-sided Gaussian mass bound $s^n/\det\Lambda<\rho_s(\Lambda)\le\max\{1,s^n\}\rho(\Lambda)$ (corrected: n ≥ 1)
-- statement:
--   Let $n\ge1$, let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice and let $s>0$. Write $\rho_s(\Lambda)=\sum_{\lambda\in\Lambda}e^{-\pi\|\lambda\|^2/s^2}$ and $\rho(\Lambda)=\rho_1(\Lambda)$. Then
--   $$\frac{s^n}{\det\Lambda}<\rho_s(\Lambda)\le\max\{1,s^n\}\,\rho(\Lambda).$$
--
--   Both bounds are used in the proof of Lemma 3.4: the lower bound at $s=\sqrt e$ shows that the potential $\Phi_\Lambda$ exceeds $1/(2e)$ at $A=e\,\mathrm{Id}$, and the upper bound controls $\Phi_\Lambda$ for matrices of large trace.
--
--   Differences from the source:
--   - correction: for any full rank lattice Λ ⊆ Rⁿ → additionally 1 ≤ n; reason: for n = 0, Λ = {0} has det Λ = 1 and ρ_s(Λ) = 1, so the strict lower bound reads 1 < 1 and fails; every use in the paper has n ≥ 1
--   - encoding: det Λ → ZLattice.covolume Λ; reason: the volume of a fundamental domain, equal to |det(b₁,…,bₙ)|; same instances
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, Lemma 2.5, p. 8

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_Gaussian

namespace LogConcaveLattice.Lift

/-- **Lemma 2.5** (p. 8), with the minimal correction `1 ≤ n`: for every full-rank lattice
`Λ ⊆ ℝⁿ` and `s > 0`, `sⁿ / det Λ < ρ_s(Λ) ≤ max{1, sⁿ} ρ(Λ)`. -/
theorem lemma_2_5 (n : ℕ) (hn : 1 ≤ n) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (s : ℝ) (hs : 0 < s) :
    s ^ n / ZLattice.covolume Λ < rhoScalarMass s Λ ∧
      rhoScalarMass s Λ ≤ max 1 (s ^ n) * rhoScalarMass 1 Λ := by sorry

end LogConcaveLattice.Lift
