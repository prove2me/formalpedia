-- Prove2me | Theorems.Thm_Monodromy_Logarithm_transport_translation
-- name    : Monodromy.Logarithm.transport_translation
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:43:15.151938+00:00
-- url     : https://prove2.me/theorems/4550a903-90e6-4561-b7ff-a23080354138
-- title:
--   Every Circle Loop Translates All Logarithm Sheets by One Common Integer
-- statement:
--   For every continuous loop γ in the circle based at 1 and every integer k, let n_γ be the integer label of the exponential-covering transport of sheet 0 along γ, where sheet k is the real lift coordinate 2πk. Then transporting sheet k along γ gives sheet(k+n_γ). Thus the same loop displacement applies to all integer sheets, including negative k.
--
--   Statement dependencies: `Monodromy.Logarithm.Memory`, `Monodromy.Logarithm.integers`, `Monodromy.Logarithm.sheet`, `Monodromy.Transport.Fiber`, `Monodromy.Transport.transport`.
--
--   Original proof dependencies: `Monodromy.Logarithm.Memory`, `Monodromy.Logarithm.integers`, `Monodromy.Logarithm.sheet`, `Monodromy.Transport.Fiber`, `Monodromy.Transport.mapFiber`, `Monodromy.Transport.transport`, `Monodromy.Transport.transport_naturality`.
--
--   Statement elaboration dependencies: `Monodromy.Logarithm.Memory`, `Monodromy.Logarithm.integers`, `Monodromy.Logarithm.sheet`, `Monodromy.Transport.Fiber`, `Monodromy.Transport.transport`.
--
--   Proof elaboration dependencies: `Monodromy.Logarithm.Memory`, `Monodromy.Logarithm.integers`, `Monodromy.Logarithm.sheet`, `Monodromy.Transport.Fiber`, `Monodromy.Transport.mapFiber`, `Monodromy.Transport.transport`, `Monodromy.Transport.transport_naturality`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Logarithm.lean (file SHA-256 7c717767a34b9975b34b033cf81fed276c1e642f6bb7abceab23baba8a3ee1d1):
--   Monodromy.Logarithm.transport_translation at L69-L90 [UTF-8 2608:3733].

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
open Monodromy.Logarithm
open unitInterval

theorem Monodromy.Logarithm.transport_translation (γ : Path (1 : Circle) 1) (k : ℤ) :
    Transport.transport Circle.isCoveringMap_exp γ (sheet k) =
      sheet (k + integers.symm
        (Transport.transport Circle.isCoveringMap_exp γ (sheet 0))) := by sorry
