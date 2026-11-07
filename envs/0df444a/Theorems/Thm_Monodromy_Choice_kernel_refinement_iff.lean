-- Prove2me | Theorems.Thm_Monodromy_Choice_kernel_refinement_iff
-- name    : Monodromy.Choice.kernel_refinement_iff
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:27:12.626068+00:00
-- url     : https://prove2.me/theorems/baa2678b-1431-4a06-a1b6-3c6d9c570463
-- title:
--   Kernel Refinement Is Equivalent to Exhausting the Inner Fiber
-- statement:
--   Let J be a finite type, f,g:ℂ→ℂ, p∈ℂ, and c:J→ℂ be injective with g(c_j)=p. Assume f has nonzero complex derivative at p and f∘g has nonzero complex derivative at every c_j. For the normalized divided-difference kernels, the identity $K_f(p,g(z))=\sum_jK_{f\circ g}(c_j,z)$ for every z satisfying f(g(z))=f(p) holds if and only if every z with g(z)=p equals c_j for some j.
--
--   Statement dependencies: `Monodromy.Choice.kernel`.
--
--   Original proof dependencies: `Monodromy.Choice.dispatch`, `Monodromy.Choice.dispatch_root`, `Monodromy.Choice.kernel`, `Monodromy.Choice.kernel_other`, `Monodromy.Choice.kernel_self`.
--
--   Statement elaboration dependencies: `Monodromy.Choice.kernel`.
--
--   Proof elaboration dependencies: `Monodromy.Choice.dispatch`, `Monodromy.Choice.dispatch_root`, `Monodromy.Choice.kernel`, `Monodromy.Choice.kernel_other`, `Monodromy.Choice.kernel_self`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Choice.lean (file SHA-256 8a1a9f2a8ef9368bf53e96d2efef8d2dd1fdc3cf5902d543a2564263e0522aec):
--   Monodromy.Choice.kernel_refinement_iff at L253-L294 [UTF-8 10914:12848].

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

theorem Monodromy.Choice.kernel_refinement_iff {κ : Type*} [Fintype κ]
    {f g : ℂ → ℂ} {parent : ℂ} (children : κ → ℂ)
    (distinct : Function.Injective children)
    (projects : ∀ child, g (children child) = parent)
    (regular : deriv f parent ≠ 0)
    (children_regular : ∀ child, deriv (f ∘ g) (children child) ≠ 0) :
    (∀ z, f (g z) = f parent →
      kernel f parent (g z) = ∑ child, kernel (f ∘ g) (children child) z) ↔
      ∀ z, g z = parent → ∃ child, children child = z := by sorry
