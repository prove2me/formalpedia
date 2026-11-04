-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_weighted_generated_eq_ambient
-- name    : OAI.FreeGroupFactorMain.WeightedFock.weighted_generated_eq_ambient
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:56:16.251618+00:00
-- url     : https://prove2.me/theorems/10bcbb67-5c19-4d3c-a56c-72075b526928
-- title:
--   The weighted Gaussian algebra is the represented corner
-- statement:
--   Fix real numbers $0<v<u$. Consider the full two-vertex path Fock space with edge labels in $\mathbb N$, the operators $S_i=uc_{i,\mathrm{true}}+vc_{i,\mathrm{false}}+\text{h.c.}$ built from creation operators, the coordinate projection $P$ onto paths starting at the vertex $\mathrm{true}$, and the ambient von Neumann algebra $\{P,S_i\}''$. Let $\mathrm{PRange}$ be the range of $P$, and let $\mathrm{representedAmbient}(u,v)$ be the corner of the ambient algebra by $P$, represented on $\mathrm{PRange}$. Let $\mathcal X$ be the weighted Gaussian system on $\mathrm{PRange}$ with the restricted vacuum as root, and let $\sigma$ be the scalar flip of its index set. Then
--
--   $$W^*(\mathcal X,\sigma)=\mathrm{representedAmbient}(u,v),$$
--
--   where $W^*(\mathcal X,\sigma)$ is the double commutant of the generators of $\mathcal X$. This identifies a corner of the weighted model with a free Gaussian algebra, the key step toward the scaling formula.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.WeightedFock.weighted_generated_eq_ambient`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/InterpolatedFactors/ScalarGeneration.lean#L431

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.FreeFock

section
open scoped ENNReal
variable {α : Type u_1} [DecidableEq α]

end
section
open scoped ENNReal ComplexConjugate
variable {α : Type u_2} [DecidableEq α]

end
open GaussianRecognition CyclicSpectral CircularRotation
open Filter Topology
open scoped ENNReal
variable {α : Type u_5} [DecidableEq α]

end FreeGroupFactorMain.FreeFock

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification WeightedCornerIndex GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem weighted_generated_eq_ambient :
    (weightedSystem u v hv hvu).generated scalarFlip=representedAmbient u v := by
  sorry

end FreeGroupFactorMain.WeightedFock
end
end OAI
