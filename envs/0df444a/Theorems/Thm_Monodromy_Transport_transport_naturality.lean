-- Prove2me | Theorems.Thm_Monodromy_Transport_transport_naturality
-- name    : Monodromy.Transport.transport_naturality
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:39:11.567305+00:00
-- url     : https://prove2.me/theorems/b1698eb7-b253-4b35-912f-7d093f96a774
-- title:
--   Continuous Covering Maps Commute with Path Transport
-- statement:
--   Let E,E′,X be topological spaces, p:E→X and q:E′→X covering maps, and h:E→E′ continuous with q∘h=p. For any x,y∈X, continuous path γ from x to y, and e∈p⁻¹({x}), transporting h(e) along γ in q’s covering equals h applied to the transport of e along γ in p’s covering. Both sides are points of q⁻¹({y}).
--
--   Statement dependencies: `Monodromy.Transport.Fiber`, `Monodromy.Transport.mapFiber`, `Monodromy.Transport.transport`.
--
--   Original proof dependencies: `Monodromy.Transport.Fiber`, `Monodromy.Transport.continuous_lift_exists`, `Monodromy.Transport.mapFiber`, `Monodromy.Transport.transport`, `Monodromy.Transport.transport_eq_actual_lift`.
--
--   Statement elaboration dependencies: `Monodromy.Transport.Fiber`, `Monodromy.Transport.mapFiber`, `Monodromy.Transport.transport`.
--
--   Proof elaboration dependencies: `Monodromy.Transport.Fiber`, `Monodromy.Transport.continuous_lift_exists`, `Monodromy.Transport.mapFiber`, `Monodromy.Transport.transport`, `Monodromy.Transport.transport_eq_actual_lift`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Covering.lean (file SHA-256 aefdaceefa095ff0e469f6766ca5bf2502b71b887c244e8f6be18ed5d8448b0c):
--   Monodromy.Transport.transport_naturality at L124-L147 [UTF-8 5223:6346].

module
public import Definitions.Def_Monodromy_Covering
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.Transport
open unitInterval
universe u v w
variable {E : Type u} {X : Type v}
variable [TopologicalSpace E] [TopologicalSpace X]
variable {p : E → X}
variable {E' : Type w} [TopologicalSpace E'] {q : E' → X}

theorem Monodromy.Transport.transport_naturality (cov : IsCoveringMap p) (cov' : IsCoveringMap q)
    (h : C(E, E')) (square : q ∘ h = p) {x y : X}
    (γ : Path x y) (e : Fiber p x) :
    transport cov' γ (mapFiber h square e) =
      mapFiber h square (transport cov γ e) := by sorry
