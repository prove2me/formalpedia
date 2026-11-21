-- Prove2me | Theorems.Thm_MomentSearch_rakhmanov_triangle_phase_geometry
-- name    : MomentSearch.rakhmanov_triangle_phase_geometry
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-21T00:10:58.96463+00:00
-- url     : https://prove2.me/theorems/3e952e8a-d2cd-4df6-972e-b2c20823b01e
-- title:
--   Sector and derivative bounds for Rakhmanov’s triangle phase
-- statement:
--   Let $1\le k<N$, $r=\sqrt{1-(k/N)^2}$, $s=(1-i\sqrt3)/2$, and $Z(t)=r(1-st)$ for $0\le t\le 2$. Using the principal square root and arctangent, define the complex phase
--   $$
--   B(t)=2iNrs\int_0^t\arctan\!\left(\frac Nk\sqrt{r^2-Z(v)^2}\right)\,dv.
--   $$
--   Then $B$ is continuous. Its real part $R$ has $R(0)=0$ and a continuous derivative on the open interval that extends continuously to the endpoints. On the open interval and closed interval, respectively, the estimates are
--   $$
--   \frac{R(t)}{t}\le R'(t)\quad(0<t<2),
--   \qquad
--   \sqrt3\,|\operatorname{Im}B(t)|\le R(t)\quad(0\le t\le 2).
--   $$
--   These are the phase-sector bound and the consequence of convexity used to estimate the triangle-side integral in Rakhmanov's proof.
-- source:
--   E. A. Rakhmanov, Bounds for polynomials with a unit discrete norm, Annals of Mathematics 165 (2007), §3.3, Lemma 5 and equations (3.20), (3.23)–(3.25), pp. 78–80. https://annals.math.princeton.edu/wp-content/uploads/annals-v165-n1-p03.pdf

import Mathlib

theorem MomentSearch.rakhmanov_triangle_phase_geometry (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
    let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
    ∃ d : ℝ → ℝ,
      ContinuousOn B (Set.Icc 0 2) ∧ ContinuousOn d (Set.Icc 0 2) ∧
      (B 0).re = 0 ∧
      (∀ t ∈ Set.Ioo 0 2, HasDerivAt (fun u => (B u).re) (d t) t) ∧
      (∀ t ∈ Set.Ioo 0 2, (B t).re / t ≤ d t) ∧
      ∀ t ∈ Set.Icc 0 2, Real.sqrt 3 * |(B t).im| ≤ (B t).re := by sorry
