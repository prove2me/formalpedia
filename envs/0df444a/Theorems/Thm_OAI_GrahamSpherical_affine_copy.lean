-- Prove2me | Theorems.Thm_OAI_GrahamSpherical_affine_copy
-- name    : OAI.GrahamSpherical.affine_copy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:11:26.807394+00:00
-- url     : https://prove2.me/theorems/7eaf69e2-1b4c-41b1-bc36-44c0464df6f8
-- title:
--   Every isometric copy of the twelve-point witness is an affine image under an orthonormal frame
-- statement:
--   Let $t=\sum_{m\ge1}10^{-m!}$ (a Liouville number), $u=\frac{1-t^2}{1+t^2}$ and $v=\frac{2t}{1+t^2}$, so $u^2+v^2=1$. The witness consists of twelve points of the unit circle, labelled by $(k,q)\in\{0,1,2\}\times\{0,1,2,3\}$: the square $Q=\{(1,0),(-1,0),(0,1),(0,-1)\}$ rotated by the angle with cosine $u$ and sine $v$ ($k=0$), rotated by the opposite angle ($k=1$), and unrotated ($k=2$). The weight of a label is $1$ for $k=0,1$ and $-2$ for $k=2$. Write $(x_i,y_i)$ for the coordinates of the witness point $P_i$.
--
--   Let $n\in\mathbb{N}$ and let $Y_i\in\mathbb{R}^n$ satisfy $\|Y_i-Y_j\|=\|P_i-P_j\|$ for all labels $i,j$. Then there are $c,A,B\in\mathbb{R}^n$ with $\|A\|=\|B\|=1$, $\langle A,B\rangle=0$ and
--   $$
--   Y_i=c+x_iA+y_iB\quad\text{for every label }i .
--   $$
--
--   No affine hypothesis or lower bound on the ambient dimension is assumed. Distance preservation alone forces the copy to be a rigid planar embedding.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SphericalRamsey/AffineCopy.lean#L19-L70

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
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_MonochromaticObstruction

open OAI OAI.GrahamSpherical
open scoped RealInnerProductSpace BigOperators

theorem OAI.GrahamSpherical.affine_copy {n : ℕ} (y : Label → Point n)
    (hy : ∀ i j, dist (y i) (y j) = dist (vertex i) (vertex j)) :
    ∃ c A B : Point n, (inner ℝ (A) (A)) = 1 ∧ (inner ℝ (B) (B)) = 1 ∧
      (inner ℝ (A) (B)) = 0 ∧ ∀ i, y i = c + coordinates i 0 • A + coordinates i 1 • B := by sorry
