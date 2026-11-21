-- Prove2me | Theorems.Thm_MasulloAudit_truncated_prime_differences_have_full_closed_span
-- name    : MasulloAudit.truncated_prime_differences_have_full_closed_span
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:14:57.683192+00:00
-- url     : https://prove2.me/theorems/e1ab1853-5589-4416-9a2d-78f585fc3142
-- title:
--   Every finite product of prime-step differences has full closed image after a lower radial cutoff
-- statement:
--   On $E=L^2(\mathbb R,(1+t^2)\,dt)$ let $M_S$ be multiplication by the indicator of a measurable subset $S\subseteq[a,\infty)$. Write $D_hf(t)=f(t)-f(t+h)$. For every finite list of positive shifts $h_1,\dots,h_m$ and every dense set $X\subset E$ one has
--   $$\overline{M_S D_{h_1}\cdots D_{h_m}(X)}=M_S(E).$$
--   This includes the empty product, either cutoff from (9.3.3.4)–(9.3.3.5), and every choice of their widths. For $F=\mathbb Q$, the trivial norm-one isotype, and $s=2$, the draft identifies its completed orbital source with this weighted norm-coordinate space. Taking the empty set of primes and then $\{2\}$ ($h=\log 2$) gives equal truncated closed images at every width, contradicting the strict-subsequence assertion for (11.1.2.6) under that identification.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Theorem 11.1.2.1(2), (11.1.2.6), pp. 480–482. See the rational radial identification in the proof of Proposition 11.2.0.1, pp. 484–485, and (9.3.3.4)–(9.3.3.5) for the masks. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Mathlib

open MeasureTheory Set Filter Topology

theorem MasulloAudit.truncated_prime_differences_have_full_closed_span (a : ℝ) (s : Set ℝ) (hs : MeasurableSet s) (hsa : s⊆Ici a) :
    let ν : Measure ℝ := volume.withDensity (fun t : ℝ => ENNReal.ofReal (1+t^2))
    let E := Lp ℂ 2 ν
    ∃ (M : E→L[ℂ]E) (D : ℝ→E→L[ℂ]E),
      (∀ f : E, (fun x => M f x)=ᵐ[ν] s.indicator f) ∧
      (∀ (t : ℝ) (f : E), (fun x => D t f x)=ᵐ[ν] fun x => f x-f (x+t)) ∧
      ∀ (L : List ℝ), (∀ t∈L,0<t) → ∀ (X : Set E), Dense X →
        let T := L.foldr (fun t (B : E→L[ℂ]E) => (D t).comp B) (ContinuousLinearMap.id ℂ E)
        closure ((fun f => M (T f)) '' X)=Set.range M := by sorry
