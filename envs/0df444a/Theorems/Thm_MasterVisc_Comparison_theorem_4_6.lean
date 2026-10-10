-- Prove2me | Theorems.Thm_MasterVisc_Comparison_theorem_4_6
-- name    : MasterVisc.Comparison.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:47:26.196991+00:00
-- url     : https://prove2.me/theorems/7cfd7345-0cfc-49cd-a4be-329db5754c91
-- title:
--   Theorem 4.6 (Consistency), p. 960 — for V ∈ C_b^{1,1,1}(Θ), viscosity and classical (sub/super)solutions coincide
-- statement:
--   Let $G$ satisfy Assumption 3.1 and $V\in C_b^{1,1,1}(\Theta)$. Then $V$ is a viscosity solution (resp. subsolution, supersolution) of the master equation (3.1) if and only if it is a classical solution (resp. subsolution, supersolution) of (3.1), i.e.
--   $$\mathbb LV(t,\mu)=\partial_tV(t,\mu)+G\big(t,\mu,V(t,\mu),\partial_\mu V(t,\mu,\cdot),\partial_\omega\partial_\mu V(t,\mu,\cdot)\big)=\ (\text{resp. }\ge,\ \le)\ 0\quad\text{on }\Theta.$$
--
--   Consistency guarantees that the viscosity notion extends, and does not change, the classical one.
--
--   **Formalization Note.** The hypothesis $V\in C_b^{1,1,1}(\Theta)$ (Definition 2.8, built on the càdlàg extension of §2) is replaced by the class it is used through (Remark 4.3(i)): $V$ together with derivative data continuous on $\Theta$ and lying in $C_b^{1,1,1}([t_1,t_2]\times\mathcal P_L(t_1,\mu))$ for all $t_1<t_2\le T$, $L>0$, $\mu\in\mathcal P_2$. This class contains $C_b^{1,1,1}(\Theta)$, so the statement is at least as strong as printed. A classical (sub/super)solution is understood with these derivative data.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), Theorem 4.6, p. 960; Definition 3.3, p. 948; Remark 4.3(i), p. 959

import Mathlib
import Definitions.Def_MasterVisc_Comparison_Setting
import Definitions.Def_MasterVisc_Comparison_Viscosity
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MasterVisc.Comparison

/-- Theorem 4.6 (Consistency), p. 960: under Assumption 3.1, for `V ∈ C_b^{1,1,1}(Θ)` (here: data `Φ` in the
tube class), `V` is a viscosity solution (resp. subsolution, supersolution) iff it is a classical one. -/
theorem theorem_4_6 {d : ℕ} {T : ℝ≥0} (L₀ : ℝ) (G : Gen d T) (hG : Assumption31 L₀ G)
    (Φ : C111Data d T) (hΦ : IsC111bTubes Φ) :
    (IsViscSol G Φ.fn ↔ IsClassicalSub G Φ ∧ IsClassicalSuper G Φ) ∧
    (IsViscSub G Φ.fn ↔ IsClassicalSub G Φ) ∧
    (IsViscSuper G Φ.fn ↔ IsClassicalSuper G Φ) := by sorry

end MasterVisc.Comparison
