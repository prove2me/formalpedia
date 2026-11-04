-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_FreeFock_haarSpatial_mem_vonNeumann
-- name    : OAI.FreeGroupFactorMain.FreeFock.haarSpatial_mem_vonNeumann
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:59:41.997035+00:00
-- url     : https://prove2.me/theorems/e1627420-eddc-48f2-9ddf-4a94fe9410d7
-- title:
--   The Haar spatial unitary matches the group and Gaussian algebras
-- statement:
--   Let $\alpha$ be a type with decidable equality. Let $L(\mathbb F(\alpha))$ be the free group von Neumann algebra on $\ell^2(\mathbb F(\alpha))$, and let $\mathcal G(\alpha)$ be the Gaussian von Neumann algebra acting on the full Fock space over $\alpha$. Let $W:\ell^2(\mathbb F(\alpha))\to\mathcal F(\alpha)$ be the unitary built from the spectral Haar representation of $\mathbb F(\alpha)$ on Fock space, which sends $\delta_e$ to the vacuum. For every bounded operator $T$ on $\ell^2(\mathbb F(\alpha))$,
--
--   $$WTW^*\in\mathcal G(\alpha)\iff T\in L(\mathbb F(\alpha)).$$
--
--   This is the bridge between the free group factor and the free Gaussian (semicircular) algebra.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.FreeFock.haarSpatial_mem_vonNeumann`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/InterpolatedFactors/GroupBridge.lean#L929

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45 u_46 u_47 u_48
universe u_49

open Filter Topology

namespace FreeFock
open Filter Topology
open scoped ENNReal
variable {α : Type u_6} [DecidableEq α]

end FreeFock
open MeasureTheory Set CompactlySupported
open scoped ENNReal
namespace CyclicSpectral
variable {H : Type u_7} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
end CyclicSpectral

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal

namespace CyclicSpectral

section
open MeasureTheory
variable {H : Type u_19} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
section
open MeasureTheory Filter
variable {H : Type u_20} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
open MeasureTheory Filter
variable {H : Type u_21} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end CyclicSpectral
namespace FreeFock

section
open MeasureTheory
variable {α : Type u_22} [DecidableEq α]

end
open MeasureTheory
variable {α : Type u_23} [DecidableEq α]

end FreeFock
open Filter Topology
open scoped ENNReal

namespace FreeFock

section
open Filter Topology Set MeasureTheory
variable {α : Type u_25} [DecidableEq α]

end
section
open Set
variable {α : Type u_26} [DecidableEq α]

end

section
open Filter Topology
open scoped ENNReal
variable {α : Type u_28} [DecidableEq α]

end
section
open scoped ComplexConjugate
variable {α : Type u_29} [DecidableEq α]

end
section
variable {α : Type u_30} [DecidableEq α]

end
variable {α : Type u_31} [DecidableEq α]

end FreeFock
section

variable {A : Type u_32} [NormedRing A] [NormedAlgebra ℂ A]

end
namespace FreeFock

section
variable {α : Type u_33} [DecidableEq α]

end
variable {α : Type u_34} [DecidableEq α]

end FreeFock

section
variable {α : Type u_35}

end
section
variable {α : Type u_36} {G : Type u_37} [Group G]

end
namespace FreeFock
variable {α : Type u_38} [DecidableEq α]

end FreeFock

namespace CyclicUnitary
open scoped ENNReal
variable {G : Type u_42} {E : Type u_43} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (ρ : G →* (E →L[ℂ] E)) (hstar : ∀ g,star (ρ g)=ρ g⁻¹) (ξ : E)

end CyclicUnitary
namespace FreeFock
variable {α : Type u_44} [DecidableEq α]

end FreeFock

section

variable {A : Type u_45} {B : Type u_46} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
  [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]

end
open scoped ENNReal
variable {G : Type u_47} [Group G] [DecidableEq G]

namespace FreeFock
variable {α : Type u_48} [DecidableEq α]

theorem haarSpatial_mem_vonNeumann (T : GroupOperator (FreeGroup α)) :
    haarSpatial.conjStarAlgEquiv T∈gaussianAlgebra α ↔ T∈groupVonNeumann (FreeGroup α) := by
  sorry

end FreeFock
end FreeGroupFactorMain
end
end OAI
