-- Prove2me | Theorems.Thm_NumberField_Idele_aestronglyMeasurable_of_continuous_prod_maximalCompact
-- name    : NumberField.Idele.aestronglyMeasurable_of_continuous_prod_maximalCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/f5d8bbba-c56f-5ab3-b8a4-7d47da86c8cd
-- title:
--   Continuous functions on A_F^×timesK are a.e. strongly measurable
-- statement:
--   Let $F$ be a number field. The adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` and its unit group are equipped with their Borel $\sigma$-algebras coming from the adelic topology, as is the subgroup $\mathbf{K} =$ `adelicMaximalCompact F` of $\mathrm{GL}_2(\mathbb{A}_F)$ consisting of those $k$ whose finite part lies in the subgroup `finiteIntegralGL2` of $\mathrm{GL}_2$ of the finite adeles (level-zero integral matrices) and whose component at each infinite place $w$ satisfies `IsRowIsometry`, i.e. has determinant of absolute value $1$ and acts on pairs $(x,y) \in w.\mathrm{Completion}^2$ preserving $\|x\|^2+\|y\|^2$ in the indicated bilinear form. Let $D \subseteq \mathbb{A}_F^\times$ be a measurable set and let $f : \mathbb{A}_F^\times \times \mathbf{K} \to \mathbb{C}$ be continuous. The assertion is that $f$ is almost everywhere strongly measurable for the product measure whose first factor is the Haar measure `idelicHaar F` on $\mathbb{A}_F^\times$ restricted to $D$ and then multiplied by the density $t \mapsto \mathrm{ofReal}\bigl(\|t\|^{-1}\bigr)$, where $\|t\|$ is `ideleNorm F t`, the module of $t$ acting on $\mathbb{A}_F$ (`distribHaarChar`), and whose second factor is the Haar measure `maximalCompactHaar F` on the compact group $\mathbf{K}$.
--
--   A measurability step in the adelic harmonic analysis underlying the automorphic-form side of the argument: it licenses integration of continuous functions against the weighted measure $\|t\|^{-1}\,d^\times t|_D \otimes dk$ occurring in the Tate-style global zeta integrals. It is used in the approximation arguments that replace an $L^p$ function on a slab by continuous, and then by band-supported and character-times-smooth, functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_aestronglyMeasurable_of_continuous_prod_maximalCompact.lean

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem NumberField.Idele.aestronglyMeasurable_of_continuous_prod_maximalCompact
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (f : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ) (hf : Continuous f) :
    AEStronglyMeasurable f ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) := by sorry
