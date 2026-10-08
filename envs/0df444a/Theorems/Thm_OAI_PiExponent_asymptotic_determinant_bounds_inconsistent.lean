-- Prove2me | Theorems.Thm_OAI_PiExponent_asymptotic_determinant_bounds_inconsistent
-- name    : OAI.PiExponent.asymptotic_determinant_bounds_inconsistent
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-07T19:02:13.671858+00:00
-- url     : https://prove2.me/theorems/97a33302-16bc-4887-9f08-17adc9990640
-- title:
--   Incompatibility of asymptotic determinant bounds
-- statement:
--   Let $\nu,\theta,x,e_{\rm ar},e_{\rm an},c_\infty$ be real constants, with $\nu>1$, and let $b_n,d_n,\varepsilon_n,c_n$ be real sequences. Assume
--
--   $$e_{\rm ar}+e_{\rm an}<\nu(x-\theta)-(1-\theta),\qquad 1+e_{\rm ar}+e_{\rm an}<c_\infty,$$
--
--   and assume that the error tends to zero and the collision rate tends to its limiting value. Then the following inequalities cannot all hold for every sufficiently large index:
--
--   $$0\le b_n\le\theta,\qquad -(1-b_n)-e_{\rm ar}\le d_n\le e_{\rm an}+\varepsilon_n+\max\{-c_n,-\nu(x-b_n)\}.$$
--
--   This is the source's general asymptotic determinant comparison lemma, useful independently of the construction of any particular interpolation matrix.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Comparison.lean#L33-L67

import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

theorem OAI.PiExponent.asymptotic_determinant_bounds_inconsistent
    (nu theta x ear ean collisionLimit : ℝ)
    (b d err collision : ℕ → ℝ)
    (hnu : 1 < nu)
    (hgap : ear + ean < nu * (x - theta) - (1 - theta))
    (hcollision : 1 + ear + ean < collisionLimit)
    (herr : Tendsto err atTop (𝓝 0))
    (hcol : Tendsto collision atTop (𝓝 collisionLimit))
    (hb0 : ∀ᶠ n in atTop, 0 ≤ b n)
    (hb : ∀ᶠ n in atTop, b n ≤ theta)
    (hlower : ∀ᶠ n in atTop, -(1 - b n) - ear ≤ d n)
    (hupper : ∀ᶠ n in atTop,
      d n ≤ ean + err n + max (-collision n) (-nu * (x - b n))) : False := by sorry
