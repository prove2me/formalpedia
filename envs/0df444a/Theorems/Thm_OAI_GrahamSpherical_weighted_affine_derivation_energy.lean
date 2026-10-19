-- Prove2me | Theorems.Thm_OAI_GrahamSpherical_weighted_affine_derivation_energy
-- name    : OAI.GrahamSpherical.weighted_affine_derivation_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:10:25.817911+00:00
-- url     : https://prove2.me/theorems/f0741750-e45c-4af3-bb98-0b8e13243b42
-- title:
--   Weighted derivation energy of an affine placement of the witness equals $8$
-- statement:
--   Let $t=\sum_{m\ge1}10^{-m!}$ (a Liouville number), $u=\frac{1-t^2}{1+t^2}$ and $v=\frac{2t}{1+t^2}$, so $u^2+v^2=1$. The witness consists of twelve points of the unit circle, labelled by $(k,q)\in\{0,1,2\}\times\{0,1,2,3\}$: the square $Q=\{(1,0),(-1,0),(0,1),(0,-1)\}$ rotated by the angle with cosine $u$ and sine $v$ ($k=0$), rotated by the opposite angle ($k=1$), and unrotated ($k=2$). The weight of a label is $1$ for $k=0,1$ and $-2$ for $k=2$. Write $(x_i,y_i)$ for the coordinates of the witness point with label $i$.
--
--   Let $D$ be a derivation of $\mathbb{R}$ over $\mathbb{Z}$ with $D(t)=\frac{1+t^2}{2}$, and let $z,A,B\in\mathbb{R}^n$ with $\sum_jA_j^2=\sum_jB_j^2=1$. Then
--   $$
--   \sum_iw_i\sum_{j=1}^n D\bigl(z_j+x_iA_j+y_iB_j\bigr)^2=8 .
--   $$
--
--   Every affine image of the witness with orthonormal-length frame vectors therefore has the same weighted energy. No orthogonality between $A$ and $B$ is needed after the moment cancellation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SphericalRamsey/EnergyIdentity.lean#L40-L59

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_Model

open OAI OAI.GrahamSpherical
open scoped BigOperators

theorem OAI.GrahamSpherical.weighted_affine_derivation_energy {n : ℕ}
    (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2)
    (z A B : Fin n → ℝ)
    (hA : ∑ j, A j ^ 2 = 1) (hB : ∑ j, B j ^ 2 = 1) :
    ∑ i : Label, (weight i : ℝ) * ∑ j : Fin n,
      (D (z j + coordinates i 0 * A j + coordinates i 1 * B j)) ^ 2 = 8 := by sorry
