-- Prove2me | Theorems.Thm_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne
-- name    : NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/217dda50-46fc-54f1-897e-80c1878d8e3f
-- title:
--   Hecke generator inverse double-coset relation at level U₁(N)
-- statement:
--   Let $L$ be a number field, $N$ an ideal of $\mathcal{O}_L$, and $S$ a finite set of finite places of $L$ (height-one primes of $\mathcal{O}_L$) such that every $v$ with $v.\mathrm{asIdeal} \mid N$ lies in $S$. The assertion is that for every finite place $w \notin S$ there are a unit $z$ of the full adele ring $\mathbb{A}_L$ and elements $u_1, u_2$ of $\mathrm{GL}_2(\mathbb{A}_L)$, each lying in the intersection of `levelOne` at $N$ with `finiteAdelicGL2Subgroup`, for which
--   $$(\,\mathrm{heckeGen}\,w\,)^{-1} = \mathrm{centralScalar}(z)\, u_1\, (\mathrm{heckeGen}\,w)\, u_2 .$$
--   Here $\mathrm{heckeGen}\,w$ is the element of $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by placing the diagonal matrix $\mathrm{diag}(\varpi_w,1)$, with $\varpi_w$ the chosen uniformiser of the completion $L_w$, in the $w$-component of the finite adeles (and the identity elsewhere); $\mathrm{centralScalar}(z)$ is the scalar matrix with entry $z$; `levelOne` at $N$ is the subgroup of $g \in \mathrm{GL}_2(\mathbb{A}_L)$ whose finite part $h$ is such that both the matrix of $h$ and that of $h^{-1}$ satisfy the predicate `IsLevelOneMatrix` at $N$ (the $\Gamma_1(N)$-type congruence condition); and `finiteAdelicGL2Subgroup` is the kernel of the map to $\mathrm{GL}_2$ of the infinite adeles, i.e. the elements with trivial archimedean component.
--
--   This is the standard relation expressing the inverse of the Hecke generator at a place $w$ outside $S$ as a central translate of a double coset of the generator itself with respect to the level $U_1(N)$ intersected with the finite-adelic points. It is used in the analysis of twisted cut traces of automorphic test functions, where it allows the contribution of $h_w^{-1}$ to be matched with that of $h_w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicLevel_exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne.lean

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

theorem NumberField.AdelicLevel.exists_heckeGen_inv_eq_centralScalar_mul_mul_heckeGen_mul_levelOne
    (L : Type) [Field L] [NumberField L]
    (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 L), v.asIdeal ∣ N → v ∈ S) :
    ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 L) L)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 L) L), u₁ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧ u₂ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L ∧
        (heckeGen (𝓞 L) L w)⁻¹ = centralScalar (𝓞 L) L z * u₁ * heckeGen (𝓞 L) L w * u₂ := by sorry
