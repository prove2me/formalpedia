-- Prove2me | Theorems.Thm_LanglandsTunnell_exists_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_of_rightConv_eq_of_ne_bot_rat
-- name    : LanglandsTunnell.exists_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_of_rightConv_eq_of_ne_bot_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/b1e094e7-4e02-5ba4-9759-a4385565cb4c
-- title:
--   Isotypic cusp forms over ℚ are archimedean Casimir eigenfunctions
-- statement:
--   Fix a character $\xi$ of the central subgroup $(\mathrm{productionPinsGeneral}\ \mathbb{Q}).Z$ of the idele class group attached to the general production pins over $\mathbb{Q}$, a nonzero ideal $N$ of $\mathcal{O}_{\mathbb{Q}}$, a finite set $S$ of height-one primes of $\mathcal{O}_{\mathbb{Q}}$, and a Hecke eigensystem $\Theta$ over $\mathbb{Q}$ with complex values (a level ideal, nonzero, together with families $a_v$, $b_v$ indexed by the height-one spectrum). Let $\varphi \colon \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ satisfy `IsIsotypicCuspFormAt` for these data: $\varphi$ is a smooth cuspidal automorphic function at the pins with central character $\xi$, is continuous, is right invariant under the level subgroup $(\mathrm{productionPinsGeneral}\ \mathbb{Q}).U\,N$, is for every $v \notin S$ an eigenfunction of the Hecke coset operator at $v$ attached to the generator $\mathrm{gen}\,v$ with eigenvalue $\Theta.a\,v$, and satisfies $\varphi(\mathrm{centralScalar}(\det(\mathrm{gen}\,v)) \cdot g) = b_v\,\varphi(g)$ for all $g$ and all $v \notin S$. Assume further that $\varphi \neq 0$; that $\varphi$ is reproduced by right convolution against some factorizable test function $\alpha$ (a product of an archimedean and a finite test factor through the two projections of $\mathrm{GL}_2$), i.e. $\int \varphi(gx)\alpha(x)\,dx = \varphi(g)$ for the adelic Haar measure; and that for every real infinite place $w$ of $\mathbb{Q}$ there is $n \in \mathbb{Z}$ with `HasArchCharacterAt₀` for $\varphi$ and the character $\mathrm{archWeightCharAt}\ hw\ n$, the $n$-th power of the basic weight character of the row-isometry subgroup at $w$. Then there exists $\lambda \in \mathbb{C}$ such that, at the unique (real) infinite place of $\mathbb{Q}$, $\varphi$ is archimedean smooth, in the sense that for every $g$ the function $e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\ hw\ e)$ is $C^\infty$ on the set of $2 \times 2$ real matrices of nonzero determinant, and $\mathrm{archCasimirAt}\ hw\ \varphi = \lambda \cdot \varphi$, where the Casimir operator is $-\bigl(\tfrac14 H^2 - \tfrac12 H + EF^{-}\bigr)$ formed from the one-parameter flow derivatives at the place.
--
--   This is the smoothness and $\mathfrak{z}$-finiteness step for automorphic forms on $\mathrm{GL}_2$ over $\mathbb{Q}$: a nonzero form with prescribed Hecke data away from $S$ and a weight at the archimedean place has a single archimedean component, so the Casimir operator acts on it by a scalar. It feeds the archimedean unitarity argument in the Langlands–Tunnell input, being cited by [`LanglandsTunnell.re_sub_eq_zero_or_im_sub_eq_zero_of_isIsotypicCuspFormAt_of_mellin_eq_archFactor_principal_of_minimalWeight`](thm.html#LanglandsTunnell.re_sub_eq_zero_or_im_sub_eq_zero_of_isIsotypicCuspFormAt_of_mellin_eq_archFactor_principal_of_minimalWeight).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_exists_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_of_rightConv_eq_of_ne_bot_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open AutomorphicForm
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker
open AutomorphicForm.CuspidalConstituent

open RealArchParam in

theorem LanglandsTunnell.exists_isArchSmoothAt_and_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_of_rightConv_eq_of_ne_bot_rat
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Θ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Θ φ)
    (hne0 : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ) :
    ∃ lam : ℂ, IsArchSmoothAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ ∧
      archCasimirAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ = lam • φ := by sorry
