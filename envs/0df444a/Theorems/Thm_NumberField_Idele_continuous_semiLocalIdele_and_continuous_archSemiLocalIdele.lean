-- Prove2me | Theorems.Thm_NumberField_Idele_continuous_semiLocalIdele_and_continuous_archSemiLocalIdele
-- name    : NumberField.Idele.continuous_semiLocalIdele_and_continuous_archSemiLocalIdele
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/2b825315-336b-53d0-87a2-43f759a7dc88
-- title:
--   Continuity of semi-local idele components, finite and archimedean
-- statement:
--   Let $K$ and $L$ be number fields with a $K$-algebra structure on $L$. The assertion is the conjunction of two continuity statements about the group $(\mathbb{A}_L)^\times$ of ideles of $L$, where $\mathbb{A}_L$ is the product of the infinite adele ring of $L$ with the finite adele ring of $\mathcal{O}_L$. First, for every $v$ in the height-one spectrum of $\mathcal{O}_K$, the homomorphism [`AutomorphicForm.TransversalMeasure.semiLocalIdele K L v`](def/AutomorphicForm_TransversalMeasure.html#L81) is continuous; by definition it sends an idele to its finite part (the units map of the second projection), and then applies the units map of the ring homomorphism $\mathbb{A}_{L}^{f}\to L\otimes_K K_v$ obtained by evaluating a finite adele at each place $w$ of $\mathcal{O}_L$ lying under-equal to $v$ and transporting the resulting element of $\prod_{w\mid v}L_w$ through the inverse of the base-change identification $L\otimes_K K_v\cong\prod_{w\mid v}L_w$. Second, for every infinite place $v$ of $K$, the homomorphism [`AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v`](def/AutomorphicForm_TransversalMeasure.html#L76) is continuous; it sends an idele to its infinite part (the units map of the first projection) and then to the tuple of its components at the infinite places $w$ of $L$ whose comap along $K\to L$ is $v$, an element of $\bigl(\prod_{w\mid v}L_w\bigr)^\times$. All groups of units carry their natural topologies.
--
--   This is the elementary statement that passing from an idele of $L$ to its semi-local component at a place of $K$ — the finite component viewed inside $(L\otimes_K K_v)^\times$, the archimedean one inside $\prod_{w\mid v}L_w^\times$ — is continuous. It serves to transport compact sets and measures from the idele group of $L$ to its semi-local factors, and is used in the construction of transversal measures and in the factorisation of integrals over the idele group into semi-local integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_continuous_semiLocalIdele_and_continuous_archSemiLocalIdele.lean

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

theorem NumberField.Idele.continuous_semiLocalIdele_and_continuous_archSemiLocalIdele
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    (∀ v : HeightOneSpectrum (𝓞 K), Continuous (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v)) ∧
    (∀ v : InfinitePlace K, Continuous (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v)) := by sorry
