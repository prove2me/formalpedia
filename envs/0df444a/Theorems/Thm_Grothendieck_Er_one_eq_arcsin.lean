-- Prove2me | Theorems.Thm_Grothendieck_Er_one_eq_arcsin
-- name    : Grothendieck.Er_one_eq_arcsin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:22:37.0552+00:00
-- url     : https://prove2.me/theorems/c8bd11a7-aa0b-4429-8ad4-c9ea267135ec
-- title:
--   The $r=1$ series is $\frac2\pi\arcsin$
-- statement:
--   At rank $1$ the paper's series is elementary. For every $t\in[-1,1]$,
--
--   $$
--   E_1(t)=\frac2\pi\arcsin t .
--   $$
--
--   This is the series side of Grothendieck's classical identity: the paper notes that at $r=1$ Lemma 2.1 reads $\mathbb E[\operatorname{sign}(Zu)\operatorname{sign}(Zv)]=\frac2\pi\arcsin(u\cdot v)$, whose series is $E_1$. Since $E_1^{-1}(t)=\sin(\tfrac\pi2 t)$ has infinite Taylor radius, rank $1$ is also the case in which the convergence-radius analysis of Section 3 is vacuous.
--
--   The statement is proved on the closed interval, endpoints included, by evaluating the coefficients through $(1/2)_k/(3/2)_k=1/(2k+1)$ and the binomial series of $(1-x^2)^{-1/2}$, then matching Mathlib's arcsine series; continuity carries the identity to $t=\pm1$. Rank $1$ is exactly the case a Laplace/Fubini argument for general rank cannot reach, so this node supplies the separate half there.
--
--   **Formalization Note** Stated for `Er 1 t` on `Set.Icc (-1) 1`; the $r=1$ counterpart of `Grothendieck.Er_one`.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Series

open MeasureTheory intervalIntegral
open scoped BigOperators Real

namespace Grothendieck

/-- **The `r = 1` case: `E_1(t) = (2/π) arcsin t` on `[-1,1]`.** This is the series side of
Grothendieck's classical identity; the `r = 1` case the general (`r ≥ 2`) argument cannot reach. -/
theorem Er_one_eq_arcsin {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    Er 1 t = 2 / Real.pi * Real.arcsin t := by sorry

end Grothendieck
