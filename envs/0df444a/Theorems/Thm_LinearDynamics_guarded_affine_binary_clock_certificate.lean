-- Prove2me | Theorems.Thm_LinearDynamics_guarded_affine_binary_clock_certificate
-- name    : LinearDynamics.guarded_affine_binary_clock_certificate
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T18:59:23.278025+00:00
-- url     : https://prove2.me/theorems/9bd215ab-b8a7-5bde-a386-8ce6632afc07
-- title:
--   Binary-clock certificates for guarded affine blocks
-- statement:
--   Consider a Boolean state vector of dimension $d$ and a transition that agrees with a fixed affine map $x\mapsto Ax+c$ whenever a specified affine guard has its expected value. Let $T$ be the clock given by a list of binary digits. Starting from the given state, check the guard on the first $\min(T,d+1)$ states of the affine orbit. Also check the power rows beginning at the identity for the homogenized $(d+1)$-by-$(d+1)$ update matrix, squaring the current power and multiplying by the update matrix when the next clock bit is one. Then the row list has one more entry than the clock bit list and its final row applied to the lifted starting state gives the exact endpoint after $T$ transitions.
-- source:
--   Application of Cayley–Hamilton to a linear observation of a homogeneous affine orbit and of binary matrix exponentiation. For the related observability method see R. E. Kalman, Mathematical Description of Linear Dynamical Systems, 1963, https://doi.org/10.1137/0301010. For binary jump-ahead see Haramoto, Matsumoto, Nishimura, Panneton and L’Ecuyer, Efficient Jump Ahead for F₂-Linear Random Number Generators, 2008, https://doi.org/10.1287/ijoc.1070.0251.

import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate

theorem LinearDynamics.guarded_affine_binary_clock_certificate {ι : Type} [Fintype ι] [DecidableEq ι]
    (mat : Matrix ι ι (ZMod 2)) (translation start : ι → ZMod 2)
    (step : (ι → ZMod 2) → (ι → ZMod 2))
    (guard : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2) (bias expected : ZMod 2)
    (onBranch : ∀ x, guard x + bias = expected → step x = mat.mulVec x + translation)
    (bits : List Bool) (powers : List (Matrix (Option ι) (Option ι) (ZMod 2))) :
    let base : Matrix (Option ι) (Option ι) (ZMod 2) := fun i j =>
      match i, j with
      | none, none => 1
      | none, some _ => 0
      | some i, none => translation i
      | some i, some j => mat i j
    let liftedStart : Option ι → ZMod 2 := fun i =>
      match i with
      | none => 1
      | some i => start i
    let time := bits.foldl (fun current bit => 2 * current + bit.toNat) 0
    (∀ i < min time (Fintype.card ι + 1),
      guard ((fun x => mat.mulVec x + translation)^[i] start) + bias = expected) →
    powers = bits.scanl (fun previous bit => previous * previous * (if bit then base else 1)) 1 →
    powers.length = bits.length + 1 ∧
    ∀ i, (powers.getLast?.getD 1).mulVec liftedStart (some i) = (step^[time] start) i := by sorry
