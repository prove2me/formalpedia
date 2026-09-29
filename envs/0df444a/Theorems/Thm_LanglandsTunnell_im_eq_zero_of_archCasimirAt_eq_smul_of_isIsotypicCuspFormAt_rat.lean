-- Prove2me | Theorems.Thm_LanglandsTunnell_im_eq_zero_of_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_rat
-- name    : LanglandsTunnell.im_eq_zero_of_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/73d718d7-6a31-5d5c-bc17-5b8c1ecf0efc
-- title:
--   Reality of the archimedean Casimir eigenvalue over ℚ
-- statement:
--   Fix a homomorphism $\xi$ from the subgroup $Z$ of the idele units attached to the pin data `productionPinsGeneral ℚ` to $\mathbb{C}^\times$, an ideal $N$ of $\mathcal{O}_\mathbb{Q}$, a finite set $S$ of height-one primes of $\mathcal{O}_\mathbb{Q}$, and a Hecke eigensystem $\Theta$ over $\mathbb{Q}$ with complex values (that is, a nonzero level ideal together with families $a_v$, $b_v$ indexed by the primes). Let $\varphi : \mathrm{GL}_2(\mathbb{A}_\mathbb{Q}) \to \mathbb{C}$ satisfy `IsIsotypicCuspFormAt`: $\varphi$ is a smooth cuspidal automorphic function for the pins with central character $\xi$, it is continuous, it is invariant under right translation by the level subgroup $U(N)$ of the pins, for every prime $v \notin S$ it is a Hecke coset eigenfunction at the generator $\mathrm{gen}(v)$ with eigenvalue $\Theta.a\,v$, and for every $v \notin S$ left translation by the central scalar $\det(\mathrm{gen}(v))$ multiplies $\varphi$ by $(\mathrm{cNorm}\,v)^{-1}\,\Theta.b\,v$. Assume $\varphi \neq 0$ and that $\varphi$ reproduces itself under right convolution against some factorizable test function $\alpha$ (a product of an archimedean and a finite test factor along the two projections), with respect to the adelic Haar measure on $\mathrm{GL}_2$. Let $\lambda \in \mathbb{C}$, assume $\varphi$ is archimedean-smooth at the real place of $\mathbb{Q}$ (for each $g$, the map sending an invertible real $2\times2$ matrix $e$ to $\varphi(g \cdot e)$ is $C^\infty$), and assume the archimedean Casimir operator at that place, namely $-\bigl(\tfrac14 H^2 - \tfrac12 H + EF^-\bigr)$ formed from the flow derivatives in the directions $H$, $E$, $F^-$, sends $\varphi$ to $\lambda\varphi$. Then $\operatorname{Im}\lambda = 0$.
--
--   This is the self-adjointness (reality) statement for the archimedean Casimir eigenvalue of a nonzero isotypic cusp form on $\mathrm{GL}_2$ over $\mathbb{Q}$, the standard symmetry of the Laplacian for the Petersson inner product. It feeds the analysis of archimedean parameters of cuspidal representations, being used in the determination of the archimedean factor for principal-series parameters of minimal weight.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_im_eq_zero_of_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_rat.lean

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
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker AutomorphicForm.CuspidalConstituent

open RealArchParam in

theorem LanglandsTunnell.im_eq_zero_of_archCasimirAt_eq_smul_of_isIsotypicCuspFormAt_rat
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Θ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Θ φ)
    (hne0 : φ ≠ 0) (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (lam : ℂ) (hsm : IsArchSmoothAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ)
    (hΩ : archCasimirAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) φ = lam • φ) :
    lam.im = 0 := by sorry
