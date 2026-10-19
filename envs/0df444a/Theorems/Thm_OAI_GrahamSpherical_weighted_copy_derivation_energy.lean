-- Prove2me | Theorems.Thm_OAI_GrahamSpherical_weighted_copy_derivation_energy
-- name    : OAI.GrahamSpherical.weighted_copy_derivation_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:11:57.777787+00:00
-- url     : https://prove2.me/theorems/f785d7ef-cabc-4c57-9555-429d01888cea
-- title:
--   Every isometric copy of the witness has weighted derivation energy $8$
-- statement:
--   Let $t=\sum_{m\ge1}10^{-m!}$ (a Liouville number), $u=\frac{1-t^2}{1+t^2}$ and $v=\frac{2t}{1+t^2}$, so $u^2+v^2=1$. The witness consists of twelve points of the unit circle, labelled by $(k,q)\in\{0,1,2\}\times\{0,1,2,3\}$: the square $Q=\{(1,0),(-1,0),(0,1),(0,-1)\}$ rotated by the angle with cosine $u$ and sine $v$ ($k=0$), rotated by the opposite angle ($k=1$), and unrotated ($k=2$). The weight of a label is $1$ for $k=0,1$ and $-2$ for $k=2$. Let $D$ be a derivation of $\mathbb{R}$ over $\mathbb{Z}$ with $D(t)=\frac{1+t^2}{2}$, and write $\mathcal{E}_D(y)=\sum_jD(y_j)^2$ for $y\in\mathbb{R}^n$.
--
--   For every isometric map $f$ from the witness into $\mathbb{R}^n$,
--   $$
--   \sum_iw_i\,\mathcal{E}_D\bigl(f(P_i)\bigr)=8 .
--   $$
--
--   The energies of any monochromatic copy would thus satisfy a fixed linear relation. This is incompatible with them all having the same colour.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SphericalRamsey/CopyInvariant.lean#L10-L34

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
open scoped BigOperators RealInnerProductSpace

theorem OAI.GrahamSpherical.weighted_copy_derivation_energy {n : ℕ}
    (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2)
    (f : witness → Point n) (hf : Isometry f) :
    ∑ i : Label, (weight i : ℝ) *
      derivationEnergy D (f ⟨vertex i, ⟨i, rfl⟩⟩) = 8 := by sorry
