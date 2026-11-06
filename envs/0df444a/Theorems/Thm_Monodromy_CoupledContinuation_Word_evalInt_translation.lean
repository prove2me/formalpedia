-- Prove2me | Theorems.Thm_Monodromy_CoupledContinuation_Word_evalInt_translation
-- name    : Monodromy.CoupledContinuation.Word.evalInt_translation
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:35:57.35551+00:00
-- url     : https://prove2.me/theorems/a313a238-21aa-4fb7-bdab-19ac9f286c77
-- title:
--   Words Without Conditional Gates Act by Their Translation at Zero
-- statement:
--   For every finite signed gate word W containing neither zeroLeft nor zeroRight in either direction, and every integer label triple λ, $W.\operatorname{evalInt}(\lambda)=\lambda+W.\operatorname{evalInt}(0)$. The addition is coordinatewise on ℤ³; the empty word and arbitrary negative label coordinates are included.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Word`, `Monodromy.CoupledContinuation.Word.ProbeFree`, `Monodromy.CoupledContinuation.Word.evalInt`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Gate`, `Monodromy.CoupledContinuation.Gate.ProbeFree`, `Monodromy.CoupledContinuation.Gate.evalInt`, `Monodromy.CoupledContinuation.Gate.evalInt_translation`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Word`, `Monodromy.CoupledContinuation.Word.ProbeFree`, `Monodromy.CoupledContinuation.Word.evalInt`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Word`, `Monodromy.CoupledContinuation.Word.ProbeFree`, `Monodromy.CoupledContinuation.Word.evalInt`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Gate`, `Monodromy.CoupledContinuation.Gate.ProbeFree`, `Monodromy.CoupledContinuation.Gate.evalInt`, `Monodromy.CoupledContinuation.Gate.evalInt_translation`, `Monodromy.CoupledContinuation.Labels`, `Monodromy.CoupledContinuation.Word`, `Monodromy.CoupledContinuation.Word.ProbeFree`, `Monodromy.CoupledContinuation.Word.evalInt`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/ForwardBoundary.lean (file SHA-256 79994010f524b607d5f4d56631e4490998ab2e44fa455569a55df12bc89c47b2):
--   Monodromy.CoupledContinuation.Word.evalInt_translation at L61-L78 [UTF-8 2446:3518].

module
public import Definitions.Def_Monodromy_ForwardBoundary
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Computability.Halting
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.CoupledContinuation

theorem Monodromy.CoupledContinuation.Word.evalInt_translation (word : Word) (free : word.ProbeFree) (labels : Labels) :
    Word.evalInt word labels = labels + Word.evalInt word 0 := by sorry
