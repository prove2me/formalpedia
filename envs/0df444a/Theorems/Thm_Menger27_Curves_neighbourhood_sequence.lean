-- Prove2me | Theorems.Thm_Menger27_Curves_neighbourhood_sequence
-- name    : Menger27.Curves.neighbourhood_sequence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:14:37.606466+00:00
-- url     : https://prove2.me/theorems/875d1215-2a8b-4a2d-8677-8fe7225e74f7
-- title:
--   p. 99 — an order-n neighbourhood sequence
-- statement:
--   Let $R$ be a compact connected regular metric curve and $p\in R$ have exact order $n$. There are open neighbourhoods $U_k$ of $p$, for $k\ge0$, such that $\overline{U_{k+1}}\subseteq U_k$, their diameters tend to zero, each boundary has exactly $n$ points, and every open neighbourhood $V$ of $p$ contained in $U_k$ has at least $n$ boundary points:
--   $$|\partial U_k|=n,\qquad |\partial V|\ge n,\qquad \operatorname{diam}(U_k)\longrightarrow0.$$
--
--   This sequence supplies the nested annuli used in Satz α. **Formalization Note** The paper first gives a version with varying $n_k$ for any regular point, then specializes to exact order $n$; this item formalizes the specialization. Compactness bounds every diameter. Lean indexes the sequence from zero rather than one.
-- source:
--   Menger, Zur allgemeinen Kurventheorie, Fund. Math. 10 (1927), p. 99, proof of the Theorem, neighbourhood sequence paragraph

import Mathlib
import Definitions.Def_Menger27_Curves_Basic

namespace Menger27.Curves

/-- The order-`n` neighbourhood sequence in the proof of the Theorem, p. 99. -/
theorem neighbourhood_sequence {X : Type*} [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X]
    (hcurve : IsRegularCurve X) (p : X) (n : ℕ) (horder : HasOrder p n) :
    ∃ U : ℕ → Set X,
      (∀ k, IsOpen (U k) ∧ p ∈ U k ∧ Bornology.IsBounded (U k) ∧
        (frontier (U k)).encard = n ∧
        (∀ V : Set X, IsOpen V → p ∈ V → V ⊆ U k →
          n ≤ (frontier V).encard) ∧
        closure (U (k + 1)) ⊆ U k) ∧
      Filter.Tendsto (fun k => Metric.diam (U k)) Filter.atTop (nhds 0) := by sorry

end Menger27.Curves
