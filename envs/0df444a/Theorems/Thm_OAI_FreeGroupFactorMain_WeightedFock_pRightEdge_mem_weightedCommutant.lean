-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_pRightEdge_mem_weightedCommutant
-- name    : OAI.FreeGroupFactorMain.WeightedFock.pRightEdge_mem_weightedCommutant
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:55:35.154921+00:00
-- url     : https://prove2.me/theorems/8d403c89-db50-43b8-a50f-8b8b78ef2770
-- title:
--   The right-edge operator commutes with the weighted generators
-- statement:
--   Fix real numbers $0<v<u$. Consider the full two-vertex path Fock space with edge labels in $\mathbb N$, the operators $S_i=uc_{i,\mathrm{true}}+vc_{i,\mathrm{false}}+\text{h.c.}$ built from creation operators, the coordinate projection $P$ onto paths starting at the vertex $\mathrm{true}$, and the ambient von Neumann algebra $\{P,S_i\}''$. Let $\mathrm{PRange}$ be the range of $P$, and let $\mathrm{representedAmbient}(u,v)$ be the corner of the ambient algebra by $P$, represented on $\mathrm{PRange}$. Let $\mathcal X$ be the weighted Gaussian system on $\mathrm{PRange}$ with the restricted vacuum as root, and let $\sigma$ be the scalar flip of its index set. Let $R$ be the operator on $\mathrm{PRange}$ obtained by compressing the right-edge operator. Then
--
--   $$R\in\{\text{generators of }\mathcal X\text{ at }\sigma\}',$$
--
--   so $R$ belongs to the commutant of the weighted Gaussian generators.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.WeightedFock.pRightEdge_mem_weightedCommutant`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/InterpolatedFactors/Cyclic.lean#L294

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.GaussianRecognition.System
variable {A : Type u_1} {E : Type u_2} {I : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification GaussianRecognition
variable {ι : Type u_4} [DecidableEq ι]

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

end

open FreeFock Amplification GaussianRecognition
variable {ι : Type u_5} [DecidableEq ι]

variable (u v : ℝ)

variable (hv : 0<v) (hvu : v<u)

theorem pRightEdge_mem_weightedCommutant :
    pRightEdge u v∈StarSubalgebra.centralizer ℂ ((weightedSystem u v hv hvu).generators scalarFlip) := by
  sorry

end FreeGroupFactorMain.WeightedFock
end
end OAI
