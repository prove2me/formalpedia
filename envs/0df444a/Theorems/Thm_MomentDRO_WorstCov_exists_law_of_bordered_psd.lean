-- Prove2me | Theorems.Thm_MomentDRO_WorstCov_exists_law_of_bordered_psd
-- name    : MomentDRO.WorstCov.exists_law_of_bordered_psd
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:37:44.281983+00:00
-- url     : https://prove2.me/theorems/0fee85c2-6281-438d-a9c8-b5043f001224
-- title:
--   §5.2, proof of Proposition 3, p. 20 — if [Λ λ; λᵀ ν] ⪰ 0 and ν > 0, a random vector with E[ζ] = λ/ν and E[ζζᵀ] = Λ/ν exists
-- statement:
--   Let $\Lambda\in\mathbb R^{n\times n}$, $\lambda\in\mathbb R^n$ and $\nu>0$ be such that
--   $$\begin{bmatrix}\Lambda&\lambda\\\lambda^{\mathsf T}&\nu\end{bmatrix}\succeq0 .$$
--   Then there is a random vector $\zeta\in\mathbb R^n$ (a Borel probability distribution on $\mathbb R^n$ with finite second moments) with
--   $$\mathbb E[\zeta]=\frac1\nu\,\lambda,\qquad \mathbb E[\zeta\zeta^{\mathsf T}]=\frac1\nu\,\Lambda .$$
--
--   In the proof of Proposition 3 this is applied to each block $(\Lambda_k^*,\lambda_k^*,\nu_k^*)$ of an optimal solution of (19) to produce the vectors $\zeta_1,\dots,\zeta_K$ whose mixture is the worst-case distribution.
--
--   **Formalization Note** $\mathbb E[\zeta\zeta^{\mathsf T}]$ is the uncentred second moment, `secondMomentAbout P 0`.
-- source:
--   Delage & Ye, Distributionally robust optimization under moment uncertainty with application to data-driven problems, authors' draft of 20 Feb 2008 (OR 58(3), 2010), p. 20, §5.2, proof of Proposition 3, construction of ζ_1, …, ζ_K

import Mathlib
import Definitions.Def_MomentDRO_WorstCov_Setting

open MeasureTheory Matrix

namespace MomentDRO.WorstCov

theorem exists_law_of_bordered_psd {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) (l : Fin n → ℝ)
    (v : ℝ) (hv : 0 < v) (hpsd : (bordered L l v).PosSemidef) :
    ∃ P : Measure (Fin n → ℝ), MomentDRO.Conf.HasSecondMoments P ∧
      MomentDRO.Conf.meanVec P = v⁻¹ • l ∧ MomentDRO.Conf.secondMomentAbout P 0 = v⁻¹ • L := by sorry

end MomentDRO.WorstCov
