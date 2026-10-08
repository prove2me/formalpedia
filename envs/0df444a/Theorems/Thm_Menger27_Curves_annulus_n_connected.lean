-- Prove2me | Theorems.Thm_Menger27_Curves_annulus_n_connected
-- name    : Menger27.Curves.annulus_n_connected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:11.384871+00:00
-- url     : https://prove2.me/theorems/ab4bab04-3076-4de7-91b9-3313e8014d6d
-- title:
--   pp. 99–100 — the annulus is n-point connected
-- statement:
--   Let $R$ be a compact connected regular metric curve and let $U',U$ be open neighbourhoods of $p$ with $\overline{U'}\subseteq U$. Suppose $|\partial U|=n$ and every open neighbourhood $V$ of $p$ contained in $U$ has $|\partial V|\ge n$. Then the compact annulus $\overline U\setminus U'$ is $n$-point connected between its outer and inner boundaries:
--   $$\operatorname{NPointConnected}(\overline U\setminus U',\partial U,\partial U',n).$$
--
--   This identifies the connectivity input to Satz β. **Formalization Note** The quantified $U,U'$ have the properties of consecutive members of the sequence on p. 99; their source-defined annulus is constructed in the conclusion, not independently supplied.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), pp. 99–100, proof of Satz α, concluding sentence “Für jedes k ist dann also” on p. 100

import Mathlib
import Definitions.Def_Menger27_Curves_Basic
import Definitions.Def_Menger27_Curves_Separation

namespace Menger27.Curves

/-- The annulus `R_k` is `n_k`-point connected, pp. 99–100. -/
theorem annulus_n_connected {X : Type*} [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X]
    (hcurve : IsRegularCurve X) (p : X) (n : ℕ)
    (U U' : Set X) (hU : IsOpen U) (hpU : p ∈ U)
    (hU' : IsOpen U') (hpU' : p ∈ U')
    (hnest : closure U' ⊆ U)
    (hboundary : (frontier U).encard = n)
    (hmin : ∀ V : Set X, IsOpen V → p ∈ V → V ⊆ U →
      n ≤ (frontier V).encard) :
    NPointConnected (closure U \ U') (frontier U) (frontier U') n := by sorry

end Menger27.Curves
