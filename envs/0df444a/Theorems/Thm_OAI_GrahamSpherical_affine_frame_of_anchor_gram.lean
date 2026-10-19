-- Prove2me | Theorems.Thm_OAI_GrahamSpherical_affine_frame_of_anchor_gram
-- name    : OAI.GrahamSpherical.affine_frame_of_anchor_gram
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:10:56.771605+00:00
-- url     : https://prove2.me/theorems/9c059cf2-a6f0-4afe-953e-e2c97755a8de
-- title:
--   Points with prescribed Gram data against three anchors lie on an affine orthonormal frame
-- statement:
--   Let $(y_i)_{i\in\iota}$ be points of $\mathbb{R}^n$, $a_i,b_i\in\mathbb{R}$, and $p,d,e\in\mathbb{R}^n$ with
--   $$
--   \langle d,d\rangle=4,\quad\langle e,e\rangle=2,\quad\langle d,e\rangle=2,
--   $$
--   and for every $i$: $\|y_i-p\|^2=(a_i-1)^2+b_i^2$, $\langle y_i-p,d\rangle=2(1-a_i)$, and $\langle y_i-p,e\rangle=1-a_i+b_i$. Then there are $c,A,B\in\mathbb{R}^n$ with $\|A\|=\|B\|=1$, $\langle A,B\rangle=0$, and
--   $$
--   y_i=c+a_iA+b_iB\quad\text{for all }i .
--   $$
--
--   This is the planar case of recovering a configuration from distances: three anchors fix a frame, and the Gram data force every point into the plane they span.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SphericalRamsey/AffineCopyCore.lean#L33-L74

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
open scoped RealInnerProductSpace

theorem OAI.GrahamSpherical.affine_frame_of_anchor_gram {ι : Type*} {n : ℕ}
    (y : ι → Point n) (a b : ι → ℝ) (p : Point n) (d e : Point n)
    (hdd : (inner ℝ (d) (d)) = 4) (hee : (inner ℝ (e) (e)) = 2) (hde : (inner ℝ (d) (e)) = 2)
    (hzz : ∀ i, (inner ℝ (y i-p) (y i-p)) = (a i-1)^2+(b i)^2)
    (hzd : ∀ i, (inner ℝ (y i-p) (d)) = 2*(1-a i))
    (hze : ∀ i, (inner ℝ (y i-p) (e)) = 1-a i+b i) :
    ∃ c A B : Point n, (inner ℝ (A) (A)) = 1 ∧ (inner ℝ (B) (B)) = 1 ∧
      (inner ℝ (A) (B)) = 0 ∧ ∀ i, y i = c + a i • A + b i • B := by sorry
