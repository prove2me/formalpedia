-- Prove2me | Theorems.Thm_OAI_GAD_scalarDeficit_sum_le
-- name    : OAI.GAD.scalarDeficit_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:22:03.76496+00:00
-- url     : https://prove2.me/theorems/ccb4d9fa-9167-4eeb-9f6d-4ffbdb606734
-- title:
--   Superadditivity of the scalar entropy deficit
-- statement:
--   For $x,y,z\ge0$ let $\lambda_\pm=\frac12\bigl((x+y+z)\pm\sqrt{(x+y+z)^2-4yz}\bigr)$ and define the scalar entropy deficit
--   $$\Delta(x,y,z)=\eta(x)+\eta(y)+\eta(z)-\eta(\lambda_+)-\eta(\lambda_-),\qquad\eta(w)=-w\log w .$$
--   Let $s$ be a finite set of indices, and let $x_i,y_i,z_i$ be real numbers with $x_i,y_i,z_i\ge0$ for all $i\in s$. Then $\Delta$ is superadditive:
--
--   $$
--   \sum_{i\in s}\Delta(x_i,y_i,z_i)\le\Delta\Bigl(\sum_{i\in s}x_i,\ \sum_{i\in s}y_i,\ \sum_{i\in s}z_i\Bigr).
--   $$
--
--   For $s=\varnothing$ both sides vanish. In the entropy inequality for Gram matrices of block matrices with a zero block, the entropy defect is first bounded by a sum of scalar deficits of diagonal entries; superadditivity collapses that sum into a single deficit of the total masses, so that the final bound depends only on squared Frobenius norms.
--
--   **Formalization Note** $\Delta$ is `scalarDeficit`; the index type is arbitrary, $s$ is a `Finset`, and nonnegativity is required only on $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/ScalarDeficit.lean#L308-L324

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open Matrix Set
open scoped BigOperators ComplexOrder
open Matrix Set

theorem OAI.GAD.scalarDeficit_sum_le {ι : Type u_2} (s : Finset ι) (x y z : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∑ i ∈ s, scalarDeficit (x i) (y i) (z i) ≤
      scalarDeficit (∑ i ∈ s, x i) (∑ i ∈ s, y i) (∑ i ∈ s, z i) := by sorry
