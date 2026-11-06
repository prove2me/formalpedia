-- Prove2me | Theorems.Thm_Monodromy_Choice_commute_of_transitive_commuting
-- name    : Monodromy.Choice.commute_of_transitive_commuting
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:26:35.985289+00:00
-- url     : https://prove2.me/theorems/cb44e4bd-c6cc-464b-b5e7-75e26c520e9c
-- title:
--   Equivariant Maps Commute Under a Transitive Commuting Family
-- statement:
--   Let H and S be arbitrary types and A:H→(S→S) a family of self-maps. Suppose every x,y∈S satisfy A_h(x)=y for some h∈H, and every two maps A_h,A_k commute. If f,g:S→S each commute with every A_h, then f and g commute: $f\circ g=g\circ f$. No group structure on H is assumed.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Choice.lean (file SHA-256 8a1a9f2a8ef9368bf53e96d2efef8d2dd1fdc3cf5902d543a2564263e0522aec):
--   Monodromy.Choice.commute_of_transitive_commuting at L300-L316 [UTF-8 12900:14053].

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

theorem Monodromy.Choice.commute_of_transitive_commuting {H S : Type*} (action : H → S → S)
    (transitive : ∀ first second, ∃ symmetry, action symmetry first = second)
    (commuting : ∀ first second, Function.Commute (action first) (action second))
    (f g : S → S) (f_equivariant : ∀ symmetry, Function.Commute f (action symmetry))
    (g_equivariant : ∀ symmetry, Function.Commute g (action symmetry)) : Function.Commute f g := by sorry
