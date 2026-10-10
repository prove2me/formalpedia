-- Prove2me | Theorems.Thm_MasterVisc_Comparison_proposition_4_12
-- name    : MasterVisc.Comparison.proposition_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:48:23.756776+00:00
-- url     : https://prove2.me/theorems/e5cd07c5-165a-47a6-a290-6b7dee6c0bab
-- title:
--   Proposition 4.12, p. 965 — if 𝒰̲_g ≠ ∅ and V̲ ∈ C⁰(Θ), then V̲ is a viscosity subsolution
-- statement:
--   Let $G$ satisfy Assumption 3.1, $g\in C^0(\mathcal P_2;\mathbb R)$, and $\underline{\mathcal U}_g\neq\emptyset$. If the lower Perron envelope
--   $$\underline V(t,\mu)=\sup\{\psi(t,\mu):\psi\in\underline{\mathcal U}_g\}$$
--   of (4.17) is in $C^0(\Theta)$, then $\underline V$ is a viscosity subsolution of the master equation (3.1).
--
--   By symmetry the upper envelope $\overline V$ is a viscosity supersolution when it is continuous; together these give the existence half of Theorem 4.13.
--
--   **Formalization Note.** "$\underline V\in C^0(\Theta)$" is stated as: there is a real-valued $v\in C^0(\Theta)$ with $\underline V(t,\mu)=v(t,\mu)$ on $\Theta$ (so $\underline V$ is finite there); the conclusion is about $v$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Proposition 4.12, p. 965, with (4.17)–(4.18), pp. 964–965

import Mathlib
import Definitions.Def_MasterVisc_Comparison_Setting
import Definitions.Def_MasterVisc_Comparison_Viscosity
import Definitions.Def_MasterVisc_Comparison_Perron
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MasterVisc.Comparison

/-- Proposition 4.12, p. 965: under Assumption 3.1, for `g ∈ C⁰(𝒫₂, ℝ)` with `𝒰̲_g ≠ ∅`, if `V̲ ∈ C⁰(Θ)`
then `V̲` is a viscosity subsolution of (3.1). -/
theorem proposition_4_12 {d : ℕ} {T : ℝ≥0} (L₀ : ℝ) (G : Gen d T) (hG : Assumption31 L₀ G)
    (g : Measure (Path d T) → ℝ) (hg : IsC0P2 g)
    (hU : ∃ (ψ : ℝ≥0 → Measure (Path d T) → ℝ) (D : PWData d T), InUunder G g ψ D)
    (v : ℝ≥0 → Measure (Path d T) → ℝ) (hv : IsC0Θ v)
    (hVv : ∀ t μ, t ≤ T → IsP2 μ → Vunder G g t μ = (v t μ : EReal)) :
    IsViscSub G v := by sorry

end MasterVisc.Comparison
