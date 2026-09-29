-- Prove2me | Theorems.Thm_Larmor_retarded_time_unique
-- name    : Larmor.retarded_time_unique
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T01:10:01.431696+00:00
-- url     : https://prove2.me/theorems/32e7429d-aa71-4196-a71b-7c3c653b4347
-- title:
--   Uniqueness of the retarded time for subluminal motion
-- statement:
--   **Uniqueness of the retarded time.** Let $c>0$ and let the worldline $w:\mathbb{R}\to\mathbb{R}^3$ of a point charge be Lipschitz with constant $K$, where $K<c$; that is, the charge never moves faster than the speed $K$, which is strictly smaller than the speed of light. Fix an observation event $(t,x)$. If $t_1$ and $t_2$ both satisfy the retardation relation
--
--   $$t_i\le t,\qquad c\,(t-t_i)=\|x-w(t_i)\|\qquad(i=1,2),$$
--
--   then $t_1=t_2$.
--
--   In words: the backward light cone of an observation event meets a subluminal worldline in at most one point. This is what allows the Liénard–Wiechert fields to be spoken of as functions of the observation event: the phrase "the retarded time", used without further comment in every textbook derivation, is exactly this uniqueness statement.
--
--   **Formalization Note** Subluminality is expressed as a global Lipschitz bound on the worldline with a constant strictly smaller than $c$, rather than as a pointwise bound on $\|\dot w\|$; this is the form in which it is used in the derivation and it avoids any differentiability assumption on $w$.
-- source:
--   https://en.wikipedia.org/wiki/Larmor_formula — Derivation section: "The variables are all evaluated at the retarded time $t_r = t - R/c$"; J. D. Jackson, Classical Electrodynamics, 3rd ed., Wiley 1998, §14.1 (uniqueness of the retarded point for a charge moving with speed less than c).

import Definitions.Def_Larmor_lienard_wiechert

namespace Larmor

theorem retarded_time_unique (c : ℝ) (hc : 0 < c) (K : NNReal) (hK : (K : ℝ) < c)
    (w : ℝ → Vec) (hw : LipschitzWith K w) (t : ℝ) (x : Vec) (t₁ t₂ : ℝ)
    (h₁ : IsRetardedTime c w t x t₁) (h₂ : IsRetardedTime c w t x t₂) : t₁ = t₂ := by sorry

end Larmor
