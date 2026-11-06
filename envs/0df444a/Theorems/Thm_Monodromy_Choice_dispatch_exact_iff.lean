-- Prove2me | Theorems.Thm_Monodromy_Choice_dispatch_exact_iff
-- name    : Monodromy.Choice.dispatch_exact_iff
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:26:56.741615+00:00
-- url     : https://prove2.me/theorems/9f677f8f-9029-408e-96b0-ecb7850026d2
-- title:
--   Exact Kernel Readout Characterizes Distinct Regular Roots
-- statement:
--   Let I be any finite type, f:ℂ→ℂ, and r:I→ℂ satisfy f(r_i)=f(r_j) for every i,j. For the normalized divided-difference kernel K_f and its finite readout D_f(r,v;z)=∑_i K_f(r_i,z)v_i, exact readout D_f(r,v;r_i)=v_i for every complex table v and every i holds if and only if r is injective and the complex derivative of f is nonzero at every r_i. The finite index type may be empty.
--
--   Statement dependencies: `Monodromy.Choice.dispatch`.
--
--   Original proof dependencies: `Monodromy.Choice.dispatch`, `Monodromy.Choice.dispatch_root`, `Monodromy.Choice.kernel`.
--
--   Statement elaboration dependencies: `Monodromy.Choice.dispatch`.
--
--   Proof elaboration dependencies: `Monodromy.Choice.dispatch`, `Monodromy.Choice.dispatch_root`, `Monodromy.Choice.kernel`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Choice.lean (file SHA-256 8a1a9f2a8ef9368bf53e96d2efef8d2dd1fdc3cf5902d543a2564263e0522aec):
--   Monodromy.Choice.dispatch_exact_iff at L135-L157 [UTF-8 5732:6792].

module
public import Definitions.Def_Monodromy_Choice
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.Choice

theorem Monodromy.Choice.dispatch_exact_iff {ι : Type*} [Fintype ι]
    {f : ℂ → ℂ} {roots : ι → ℂ}
    (same_fiber : ∀ i j, f (roots i) = f (roots j)) :
    (∀ values : ι → ℂ, ∀ i, dispatch f roots values (roots i) = values i) ↔
      Function.Injective roots ∧ ∀ i, deriv f (roots i) ≠ 0 := by sorry
