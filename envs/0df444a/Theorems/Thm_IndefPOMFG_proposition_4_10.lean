-- Prove2me | Theorems.Thm_IndefPOMFG_proposition_4_10
-- name    : IndefPOMFG.proposition_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:45.763849+00:00
-- url     : https://prove2.me/theorems/7ac45515-3ac0-42c0-a476-ed414c10a065
-- title:
--   Proposition 4.10 — P is a relaxed compensator ⇔ P satisfies Condition (RC)
-- statement:
--   Under (H1)–(H2), a function $P\in\Upsilon([0,T];\mathbb S^n)$ is a relaxed compensator for Problem (MFD) (its compensated weights satisfy Condition (PD)) if and only if $P$ satisfies **Condition (RC)**:
--
--   $$\dot P_t+P_tA_t+A_t^\top P_t+D_t^\top P_tD_t+Q_t-(S_t+P_tB_t+D_t^\top P_tF_t)(R_t+F_t^\top P_tF_t)^{-1}(S_t+P_tB_t+D_t^\top P_tF_t)^\top\ge0,$$
--   $$P_T\le L_T,\qquad R_t+F_t^\top P_tF_t\gg0,\qquad t\in[0,T].$$
--
--   (RC) is a system of matrix inequalities in the coefficients only, so a relaxed compensator can be checked without solving a Riccati equation.
--
--   Differences from the source:
--   - encoding: L^∞([0,T]; ·) = deterministic uniformly bounded functions (p.5), L²([0,T]; ·) square integrable → Borel functions of time bounded by a constant at every t ∈ [0,T] (L²: Borel and square integrable); reason: p.5's own definition; Borel measurability fixes the representative so coefficient-times-process integrands are progressive
--   - reading: Υ([0,T]; 𝕊ⁿ) = {P : P_t = P₀ + ∫₀ᵗ Ṗ_s ds} (p.10), regularity of Ṗ not printed → P 𝕊ⁿ-valued on [0,T] with Ṗ Lebesgue integrable (P absolutely continuous); conditions involving Ṗ hold for some such representative Ṗ at every t; reason: the weakest reading of the printed set; Ṗ is determined only a.e.
--   - encoding: "≥ 0" for the (time-dependent) matrices of (PD) and (26) → nonnegative quadratic form ⟨Mv, v⟩ ≥ 0 at every t ∈ [0,T]; reason: Q^P involves Ṗ, symmetric only a.e.; for symmetric matrices this is positive semidefiniteness
-- source:
--   Chen, Nie & Wu, Indefinite Linear-Quadratic Partially Observed Mean-Field Game, arXiv:2508.01568v1, Proposition 4.10, Condition (RC) (26), p.11

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_IndefPOMFG_Coeffs
import Definitions.Def_IndefPOMFG_Space
import Definitions.Def_IndefPOMFG_NPlayer
import Definitions.Def_IndefPOMFG_Limiting
import Definitions.Def_IndefPOMFG_Compensator

open MeasureTheory Set Peng1990.SMP
open scoped NNReal ENNReal Matrix

namespace IndefPOMFG

/-- Proposition 4.10 (Chen–Nie–Wu, arXiv:2508.01568v1, p.11): under (H1)–(H2), a function
`P ∈ Υ([0, T]; 𝕊ⁿ)` is a relaxed compensator for Problem (MFD) if and only if `P` satisfies
Condition (RC), (26). -/
theorem proposition_4_10 {n m d : ℕ} (c : Coeffs n m d) (h1 : H1 c) (h2 : H2 c)
    (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (hP : ∃ Pdot, IsUpsilon c P Pdot) :
    IsRelaxedCompensator c P ↔ CondRC c P := by sorry

end IndefPOMFG
