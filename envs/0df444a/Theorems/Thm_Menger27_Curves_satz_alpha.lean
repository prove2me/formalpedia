-- Prove2me | Theorems.Thm_Menger27_Curves_satz_alpha
-- name    : Menger27.Curves.satz_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:57.604495+00:00
-- url     : https://prove2.me/theorems/51ae7dd7-767d-444f-b14d-e4c31ee84348
-- title:
--   Satz α — disjoint arcs across a nested annulus
-- statement:
--   Let $R$ be a compact connected regular metric curve. Let $U',U$ be open neighbourhoods of $p$ with $\overline{U'}\subseteq U$, $|\partial U|=n$, and every open neighbourhood $V\subseteq U$ of $p$ having at least $n$ boundary points. Then $\overline U\setminus U'$ contains $n$ pairwise disjoint arcs, each joining a point of $\partial U$ to a point of $\partial U'$:
--   $$\gamma_i(0)\in\partial U,\quad\gamma_i(1)\in\partial U',\quad\gamma_i([0,1])\subseteq\overline U\setminus U'.$$
--
--   The arcs in successive annuli are the stated input to the paper's main Theorem. **Formalization Note** The general open sets $U,U'$ carry the properties of consecutive chosen neighbourhoods, making the paper's implicit conditions explicit. The ranges of distinct arcs are disjoint, including endpoints.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 99, Satz α

import Mathlib
import Definitions.Def_Menger27_Curves_Basic

namespace Menger27.Curves

/-- Satz α, p. 99: disjoint arcs cross each annulus. -/
theorem satz_alpha {X : Type*} [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X]
    (hcurve : IsRegularCurve X) (p : X) (n : ℕ)
    (U U' : Set X) (hU : IsOpen U) (hpU : p ∈ U)
    (hU' : IsOpen U') (hpU' : p ∈ U')
    (hnest : closure U' ⊆ U)
    (hboundary : (frontier U).encard = n)
    (hmin : ∀ V : Set X, IsOpen V → p ∈ V → V ⊆ U →
      n ≤ (frontier V).encard) :
    ∃ γ : Fin n → unitInterval → X,
      (∀ i, IsArc (γ i) ∧ γ i 0 ∈ frontier U ∧
        γ i 1 ∈ frontier U' ∧ Set.range (γ i) ⊆ closure U \ U') ∧
      ∀ i j, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j)) := by sorry

end Menger27.Curves
