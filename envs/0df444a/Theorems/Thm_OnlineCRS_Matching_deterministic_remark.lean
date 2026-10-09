-- Prove2me | Theorems.Thm_OnlineCRS_Matching_deterministic_remark
-- name    : OnlineCRS.Matching.deterministic_remark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:10.903845+00:00
-- url     : https://prove2.me/theorems/222885bd-2bc1-4a8b-bc56-cad0afb3f33e
-- title:
--   Remark, p. 14 — with K = E the greedy OCRS of all matchings is (b, (1 − b)²)-selectable
-- statement:
--   Let $G=(V,E)$ be a finite loopless graph and $b\in[0,1]$. Consider the deterministic greedy OCRS that, for every $x$, uses the family of **all** matchings of $G$ (the scheme of Theorem 2.7 with $K=E$). It is $(b,(1-b)^2)$-selectable for $P_G$: for every $x\in bP_G$ and every edge $g\in E$,
--
--   $$\Pr_{A\sim R(x)}\big[g\text{ is selectable for }A\text{ and the family of all matchings}\big]\ \ge\ (1-b)^2.$$
--
--   This is the deterministic counterpart of Theorem 2.7, with the guarantee $(1-b)^2$ in place of $e^{-2b}$.
-- source:
--   arXiv:1508.00142v2, Remark after the proof of Theorem 2.7, p. 14

import Mathlib
import Definitions.Def_OnlineCRS_Matching_Model

namespace OnlineCRS.Matching

/-- Remark after Theorem 2.7, p. 14: taking `K = E` deterministically, the greedy OCRS whose family is
the set of all matchings of `G` is `(b, (1 − b)²)`-selectable for `P_G`. -/
theorem deterministic_remark {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    OnlineCRS.Matroid.IsSelectableDet (EdmondsMatching65.Polyhedron.IsMatching G) (matchingRelax G) b ((1 - b) ^ 2)
      (fun _ => famK G Finset.univ) := by sorry

end OnlineCRS.Matching
