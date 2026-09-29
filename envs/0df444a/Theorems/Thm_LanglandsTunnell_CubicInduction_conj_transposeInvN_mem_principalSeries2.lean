-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_conj_transposeInvN_mem_principalSeries2
-- name    : LanglandsTunnell.CubicInduction.conj_transposeInvN_mem_principalSeries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/5935a4c9-1247-5b5a-b30d-e1bc61c79701
-- title:
--   Contragredient involution maps I(μ₀,μ₁) to I(μ₁⁻¹,μ₀⁻¹)
-- statement:
--   Let $p$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, and write $F = \mathbb{Q}_p$ for the corresponding completion. Let $\mu : \mathrm{Fin}\,2 \to \mathrm{Hom}(F^\times, \mathbb{C}^\times)$ be a pair of multiplicative characters of $F^\times$, and let $\varphi : \mathrm{GL}_2(F) \to \mathbb{C}$ belong to `principalSeries2 p μ`, that is: $\varphi$ is locally constant, $\varphi\bigl(\begin{pmatrix}1&x\\0&1\end{pmatrix} g\bigr) = \varphi(g)$ for all $x \in F$ and $g \in \mathrm{GL}_2(F)$, and $\varphi(\mathrm{diag}(a_0,a_1)\,g) = \mu_0(a_0)\mu_1(a_1)\,\sqrt{\lVert a_0\rVert/\lVert a_1\rVert}\;\varphi(g)$ for all $a_0,a_1 \in F^\times$, the square root being the real square root of the quotient of the two norms, coerced to $\mathbb{C}$. Let $w_0 \in \mathrm{GL}_2(F)$ be an element whose underlying matrix is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Then the function $h \mapsto \varphi\bigl(w_0 \, {}^{\mathsf T}(h^{-1}) \, w_0\bigr)$, where `transposeInvN` sends $h$ to the transpose of the inverse matrix of $h$, satisfies the same three conditions with respect to the pair of characters $(\mu_1^{-1}, \mu_0^{-1})$, i.e. it lies in `principalSeries2 p ![(μ 1)⁻¹, (μ 0)⁻¹]`. No hypothesis is imposed on $\mu$ beyond multiplicativity.
--
--   This is the statement that the contragredient involution $h \mapsto w_0\,{}^{\mathsf T}h^{-1}w_0$ of $\mathrm{GL}_2(F)$, which preserves the upper triangular Borel subgroup while inverting the torus and swapping its two coordinates, carries a vector of the normalised principal series $I(\mu_0,\mu_1)$ to a vector of $I(\mu_1^{-1},\mu_0^{-1})$. It is the rank-one counterpart of the corresponding statement for $\mathrm{GL}_3$ cell sections, and is used in the local Rankin–Selberg computations to identify the dual local integrals and functional equations attached to principal series vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_conj_transposeInvN_mem_principalSeries2.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.CubicInduction.conj_transposeInvN_mem_principalSeries2
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (φ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ : φ ∈ principalSeries2 p μ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    (fun h : GL (Fin 2) (p.adicCompletion ℚ) => φ (w₀p * transposeInvN (Fin 2) h * w₀p)) ∈
      principalSeries2 p ![(μ 1)⁻¹, (μ 0)⁻¹] := by sorry
