-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_inducedE_inducedCoeff_inv_eq_of_not_isBadPlace
-- name    : LanglandsTunnell.CubicInduction.inducedE_inducedCoeff_inv_eq_of_not_isBadPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/47bd691b-9dbc-5f42-a856-1ee5cfc7c1a0
-- title:
--   Contragredient Euler parameters at a good place
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$, whose ring of integers is an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, let $\mu \colon (\mathbb{A}_K)^{\times} \to \mathbb{C}^{\times}$ be a group homomorphism which is an admissible twist, i.e. $\mu$ is trivial on the image of $K^{\times}$, continuous, and unitary in the sense that $\|\mu(x)\| = 1$ for every idele unit $x$, and let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$ which is not a bad place for $(K,\mu)$: no prime $\mathfrak{P}$ in the fibre `primeFibre ℚ K v` has ramification index over $v$ different from $1$, and at every such $\mathfrak{P}$ the character $\mu$ is unramified (its local component is trivial on those units of the completion at $\mathfrak{P}$ whose inverse is also integral). For a coefficient function $c$ on the primes of $\mathcal{O}_K$, write $E_1 = -\,[X^1]$, $E_2 = [X^2]$, $E_3 = -\,[X^3]$ of the induced Euler polynomial at $v$, the finite product over `primeFibre ℚ K v` of the local factors `inducedFactor`, and take for $c$ the function $\mathfrak{P} \mapsto \mu(\varpi_{\mathfrak{P}})$ at primes where $\mu$ is unramified and $0$ elsewhere, respectively the same function formed from $\mu^{-1}$. Then, writing $e_i$ for the parameters attached to $\mu$ and $\check e_i$ for those attached to $\mu^{-1}$: $e_3 \neq 0$, $\|e_3\| = 1$, $\check e_1 = e_2 e_3^{-1}$, $\check e_2 = e_1 e_3^{-1}$, $\check e_3 = e_3^{-1}$, and $\|\check e_1\| \le 3$, $\|\check e_2\| \le 3$, $\|\check e_3\| \le 1$.
--
--   This identifies the Euler parameters of the contragredient (inverse) twist at a place of $\mathbb{Q}$ unramified in the cubic field and unramified for $\mu$: the Euler polynomial of $\mu^{-1}$ is the reciprocal of that of $\mu$, normalised by $e_3$, together with the crude archimedean bounds that follow from unitarity. It feeds the Euler-product computation of the local zeta integral of the dual Whittaker function in the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_inducedE_inducedCoeff_inv_eq_of_not_isBadPlace.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  NumberField.InfinitePlace LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.inducedE_inducedCoeff_inv_eq_of_not_isBadPlace
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v) :
    inducedE3 ℚ (inducedCoeff K μ) v ≠ 0 ∧
    ‖inducedE3 ℚ (inducedCoeff K μ) v‖ = 1 ∧
    inducedE1 ℚ (inducedCoeff K μ⁻¹) v = inducedE2 ℚ (inducedCoeff K μ) v * (inducedE3 ℚ (inducedCoeff K μ) v)⁻¹ ∧
    inducedE2 ℚ (inducedCoeff K μ⁻¹) v = inducedE1 ℚ (inducedCoeff K μ) v * (inducedE3 ℚ (inducedCoeff K μ) v)⁻¹ ∧
    inducedE3 ℚ (inducedCoeff K μ⁻¹) v = (inducedE3 ℚ (inducedCoeff K μ) v)⁻¹ ∧
    ‖inducedE1 ℚ (inducedCoeff K μ⁻¹) v‖ ≤ 3 ∧ ‖inducedE2 ℚ (inducedCoeff K μ⁻¹) v‖ ≤ 3 ∧
    ‖inducedE3 ℚ (inducedCoeff K μ⁻¹) v‖ ≤ 1 := by sorry
