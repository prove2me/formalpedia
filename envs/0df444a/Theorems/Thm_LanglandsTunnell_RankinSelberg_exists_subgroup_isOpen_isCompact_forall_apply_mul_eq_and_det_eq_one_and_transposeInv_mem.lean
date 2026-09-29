-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_subgroup_isOpen_isCompact_forall_apply_mul_eq_and_det_eq_one_and_transposeInv_mem
-- name    : LanglandsTunnell.RankinSelberg.exists_subgroup_isOpen_isCompact_forall_apply_mul_eq_and_det_eq_one_and_transposeInv_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/900e63f7-6341-5fd2-80e5-d266c5f8665e
-- title:
--   Open compact subgroup adapted to φ₁ and χ
-- statement:
--   Let $p$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, and write $F = \mathbb{Q}_p$ for the $p$-adic completion of $\mathbb{Q}$ at $p$. Let $\varphi_1 : M_2(F) \to \mathbb{C}$ be a function on $2\times 2$ matrices over $F$ which is locally constant and has compact support, and let $\chi : F^\times \to \mathbb{C}^\times$ be a homomorphism of monoids from the units of $F$ to the units of $\mathbb{C}$ which is locally constant as a function. The assertion is the existence of a subgroup $\Omega$ of $\mathrm{GL}_2(F)$ whose underlying set is both open and compact, such that: (i) for every $\omega \in \Omega$ and every $h \in \mathrm{GL}_2(F)$, the value of $\varphi_1$ at the matrix underlying the product $\omega h$ equals its value at the matrix underlying $h$; (ii) $\chi(\det \omega) = 1$ for every $\omega \in \Omega$, where $\det$ is the determinant as a unit of $F$; and (iii) $\Omega$ is stable under the map $g \mapsto \mathrm{transposeInvN}$ sending an invertible matrix $g$ to the invertible matrix whose underlying matrix is the transpose of that of $g^{-1}$ (with inverse the transpose of that of $g$).
--
--   This is the choice of averaging subgroup $\Omega$ made in the local Rankin–Selberg computations of Jacquet, Piatetski-Shapiro and Shalika: an open compact subgroup of $\mathrm{GL}_2(F)$ stable under $g \mapsto {}^t g^{-1}$ that leaves the Schwartz–Bruhat function $\varphi_1$ invariant under left translation and on which $\chi \circ \det$ is trivial. It is used to discharge the hypotheses on $\Omega$ in the project's results on local Rankin–Selberg integrals of Whittaker functions and on the Kirillov pairing for cuspidal forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_subgroup_isOpen_isCompact_forall_apply_mul_eq_and_det_eq_one_and_transposeInv_mem.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_subgroup_isOpen_isCompact_forall_apply_mul_eq_and_det_eq_one_and_transposeInv_mem
    (p : HeightOneSpectrum (𝓞 ℚ))
    (φ₁ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hφ₁ : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁)
    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : IsLocallyConstant χ) :
    ∃ Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
      (∀ ω ∈ Ω, ∀ h : GL (Fin 2) (p.adicCompletion ℚ),
        φ₁ ((ω * h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = φ₁ ((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ))) ∧
      (∀ ω ∈ Ω, χ (Matrix.GeneralLinearGroup.det ω) = 1) ∧
      (∀ ω ∈ Ω, transposeInvN (Fin 2) ω ∈ Ω) := by sorry
