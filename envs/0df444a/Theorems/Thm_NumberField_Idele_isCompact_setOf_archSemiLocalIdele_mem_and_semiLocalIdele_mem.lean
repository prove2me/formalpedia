-- Prove2me | Theorems.Thm_NumberField_Idele_isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem
-- name    : NumberField.Idele.isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/d2694736-904f-56ad-af06-23721f9eb50b
-- title:
--   Compactness of semi-local idele boxes in A_L^×
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra. Suppose given, for every infinite place $v$ of $K$, a set $A_v$ of units of the product ring $\prod_{w\in v.\mathrm{Extension}\,L} L_w$, where $w$ runs over the infinite places of $L$ restricting to $v$ and $L_w$ is the completion at $w$, and assume each $A_v$ is compact; let $S_f$ be a finite set of nonzero primes of $\mathcal{O}_K$, and for every nonzero prime $v$ of $\mathcal{O}_K$ a set $B_v$ of units of $L\otimes_K K_v$ ($K_v$ the adic completion), assumed compact for $v\in S_f$ only. Then the following subset of the unit group of the adele ring of $L$ is compact: the set of those $t$ whose archimedean semi-local component at each infinite place $v$ of $K$ — the infinite part of $t$ read off at the places of $L$ above $v$ — lies in $A_v$, whose semi-local component at $v\in S_f$ — the finite part of $t$ transported through the base-change isomorphism $L\otimes_K K_v\cong\prod_{w\mid v}L_w$ — lies in $B_v$, and whose semi-local component at each $v\notin S_f$ lies in the subgroup `integralUnits K L v` of units of the image of $\mathcal{O}_L\otimes_{\mathcal{O}_K}\mathcal{O}_{K_v}$ in $L\otimes_K K_v$.
--
--   This is the standard compactness criterion for a "box" in the idele group of $L$, described semi-locally over the places of $K$: arbitrary compact constraints at the archimedean places and at finitely many finite places, and the integral semi-local units elsewhere. It is used to assemble local confinement conditions into a single compact set of ideles, and is cited in the treatment of twisted orbital integrals over unramified transversals ([`AutomorphicForm.TwistedBruhat.exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_isCompact_forall_ae_mem_of_unitsAct_mul_inv_mem_of_transversal_unram)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal
open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in

theorem NumberField.Idele.isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (A : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ) (hA : ∀ v, IsCompact (A v))
    (Sf : Finset (HeightOneSpectrum (𝓞 K)))
    (B : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ) (hB : ∀ v ∈ Sf, IsCompact (B v)) :
    IsCompact {t : (AdeleRing (𝓞 L) L)ˣ |
      (∀ v : InfinitePlace K, AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t ∈ A v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sf → AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ B v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
          AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v)} := by sorry
