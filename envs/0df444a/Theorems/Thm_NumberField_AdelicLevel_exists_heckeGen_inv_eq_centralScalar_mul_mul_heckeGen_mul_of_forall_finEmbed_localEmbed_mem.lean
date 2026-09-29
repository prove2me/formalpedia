-- Prove2me | Theorems.Thm_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem
-- name    : NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/137b8618-0d40-57f6-b4f9-f41e2497a299
-- title:
--   Hecke generator inverse in a central-times-level double coset
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$, let $U$ be an arbitrary assignment of a subgroup $U(N) \le \mathrm{GL}_2(\mathbb{A}_F)$ to each ideal $N$ of $\mathcal{O}_F$, let $N$ be an ideal of $\mathcal{O}_F$ and let $S$ be a finite set of finite places of $F$. Assume (i) every finite place $v$ whose prime ideal divides $N$ lies in $S$, and (ii) for every finite place $v$ with $v \nmid N$ and every $k$ in the image of $\mathrm{GL}_2(\mathcal{O}_v)$ in $\mathrm{GL}_2(F_v)$ under the structure map (the range of the induced map on general linear groups), the adelic matrix obtained by placing $k$ at $v$ and the identity at all other finite places and at the archimedean places lies in $U(N)$. Then for every finite place $w \notin S$ there are a unit $z$ of the adele ring $\mathbb{A}_F$ and elements $u_1, u_2 \in U(N)$ such that $h_w^{-1} = \mathrm{diag}(z,z)\, u_1\, h_w\, u_2$, where $h_w$ is the adelic Hecke generator `heckeGen`, given by the matrix $\mathrm{diag}(\varpi_w, 1)$ at $w$ (for the chosen uniformiser $\varpi_w$ of $F_w$) and the identity at every other place.
--
--   This is the standard double-coset relation expressing that the inverse of the Hecke generator at a place $w$ outside $S$ lies in the double coset of the generator itself, up to a central adelic scalar. It is stated for an arbitrary level family satisfying the two hypotheses, and is specialised in [`NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne`](thm.html#NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne) and [`NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_principalLevel`](thm.html#NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_principalLevel), where it serves as an input to the trace-class estimates for adelic automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain MeasureTheory NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LocalGL2
open scoped TensorProduct Pointwise TensorProduct.RightActions ComplexConjugate BigOperators NumberField NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_of_forall_finEmbed_localEmbed_mem
    (F : Type) [Field F] [NumberField F]
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ N → v ∈ S)
    (hU : ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ N →
      ∀ k ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F),
        AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v k) ∈ U N) :
    ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 F) F)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 F) F), u₁ ∈ U N ∧ u₂ ∈ U N ∧
        (heckeGen (𝓞 F) F w)⁻¹ = centralScalar (𝓞 F) F z * u₁ * heckeGen (𝓞 F) F w * u₂ := by sorry
