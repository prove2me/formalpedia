-- Prove2me | Theorems.Thm_Monodromy_NestedContinuation_nested_curve_unique
-- name    : Monodromy.NestedContinuation.nested_curve_unique
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:37:15.852116+00:00
-- url     : https://prove2.me/theorems/67938652-b57a-4dc3-b140-9fa975b45ae1
-- title:
--   A Double-Exponential Curve and Its Initial Value Determine the Lift
-- statement:
--   For every pair of continuous complex curves f,g on the unit interval, if $\exp(\exp(f(t)))=\exp(\exp(g(t)))$ at every t and f(0)=g(0), then f=g as entire continuous curves. No avoidance hypothesis beyond the stated projected equality is assumed.
--
--   Statement dependencies: `Monodromy.NestedContinuation.Punctured`, `Monodromy.NestedContinuation.expCover`.
--
--   Original proof dependencies: `Monodromy.NestedContinuation.Punctured`, `Monodromy.NestedContinuation.covering`, `Monodromy.NestedContinuation.expCover`.
--
--   Statement elaboration dependencies: `Monodromy.NestedContinuation.Punctured`, `Monodromy.NestedContinuation.expCover`.
--
--   Proof elaboration dependencies: `Monodromy.NestedContinuation.Punctured`, `Monodromy.NestedContinuation.covering`, `Monodromy.NestedContinuation.expCover`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Logarithm.lean (file SHA-256 7c717767a34b9975b34b033cf81fed276c1e642f6bb7abceab23baba8a3ee1d1):
--   Monodromy.NestedContinuation.nested_curve_unique at L508-L522 [UTF-8 22823:23611].

module
public import Definitions.Def_Monodromy_Logarithm
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.NestedContinuation
open unitInterval

theorem Monodromy.NestedContinuation.nested_curve_unique (first second : C(I, ℂ))
    (projects : ∀ t, expCover (Complex.exp (first t)) = expCover (Complex.exp (second t)))
    (starts : first 0 = second 0) : first = second := by sorry
