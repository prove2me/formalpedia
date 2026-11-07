-- Prove2me | Theorems.Thm_Monodromy_Choice_dispatch_comp
-- name    : Monodromy.Choice.dispatch_comp
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:26:45.715199+00:00
-- url     : https://prove2.me/theorems/52aca998-a26e-4dc8-aa92-7997c3751bae
-- title:
--   Composite Kernel Readout Factors Through Inner Readouts
-- statement:
--   Let I and J be finite types, f,g:ℂ→ℂ, outer roots r_i, and complex tables c_{ij},v_{ij}. Suppose g(c_{ij})=r_i, f is complex differentiable at each r_i, and g is complex differentiable at each c_{ij}. For every w∈ℂ, the normalized-kernel readout over the composite roots satisfies $D_{f\circ g}(c,v;w)=\sum_i K_f(r_i,g(w))D_g(c_i,v_i;w)$. No distinctness or nonzero-derivative premise is required here.
--
--   Statement dependencies: `Monodromy.Choice.dispatch`, `Monodromy.Choice.kernel`.
--
--   Original proof dependencies: `Monodromy.Choice.dispatch`, `Monodromy.Choice.kernel`, `Monodromy.Choice.kernel_comp`.
--
--   Statement elaboration dependencies: `Monodromy.Choice.dispatch`, `Monodromy.Choice.kernel`.
--
--   Proof elaboration dependencies: `Monodromy.Choice.dispatch`, `Monodromy.Choice.kernel`, `Monodromy.Choice.kernel_comp`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Choice.lean (file SHA-256 8a1a9f2a8ef9368bf53e96d2efef8d2dd1fdc3cf5902d543a2564263e0522aec):
--   Monodromy.Choice.dispatch_comp at L226-L247 [UTF-8 9881:10862].

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

theorem Monodromy.Choice.dispatch_comp {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f g : ℂ → ℂ} (outerRoots : ι → ℂ) (children values : ι → κ → ℂ)
    (projects : ∀ i j, g (children i j) = outerRoots i)
    (outer : ∀ i, DifferentiableAt ℂ f (outerRoots i))
    (inner : ∀ i j, DifferentiableAt ℂ g (children i j)) (w : ℂ) :
    dispatch (f ∘ g) (fun index : ι × κ => children index.1 index.2)
      (fun index : ι × κ => values index.1 index.2) w =
      ∑ i, kernel f (outerRoots i) (g w) * dispatch g (children i) (values i) w := by sorry
