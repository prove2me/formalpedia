-- Prove2me | Theorems.Thm_McLeishCLT_MDA_trunc_integral_prodT_eq_one
-- name    : McLeishCLT.MDA.trunc_integral_prodT_eq_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:32:18.060984+00:00
-- url     : https://prove2.me/theorems/c3448186-facb-4d59-b8e6-294936eef244
-- title:
--   p. 622, proof of (2.3) — for the truncated array, E T_n = 1
-- statement:
--   Let $\{X_{n,i}\}$ be a martingale difference array with respect to row-wise filtrations $\{\mathcal F_{n,i}\}$, let $Z_{n,j}=X_{n,j}\,I(\sum_{k=1}^{j-1}X_{n,k}^2\le2)$, and for real $t$ let $T_n=\prod_{j=1}^{k_n}(1+itZ_{n,j})$. Then for every real $t$ and every $n$
--   $$E\,T_n=1 .$$
--
--   This verifies condition (2.1 a) for the truncated array in the proof of Theorem (2.3).
--
--   **Formalization Note** The expectation is a Bochner integral of a complex random variable. No moment hypothesis beyond the integrability built into the m.d.a. predicate is assumed (in particular not (2.3 a)); a non-integrable $T_n$ would give the value $0$, not $1$, so the identity is not satisfied by a junk value.
-- source:
--   McLeish, Dependent central limit theorems and invariance principles, Ann. Probab. 2 (1974), p. 622, proof of Theorem (2.3), "Then ET_n = 1"

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

namespace McLeishCLT.MDA

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- p. 622, proof of (2.3): for the truncated array, `E T_n = 1`. -/
theorem trunc_integral_prodT_eq_one {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ m0) (k : ℕ → ℕ) (X : ℕ → ℕ → Ω → ℝ)
    (hmda : IsMDA P ℱ k X) :
    ∀ (t : ℝ) (n : ℕ), ∫ ω, prodT k (trunc X) t n ω ∂P = 1 := by sorry

end McLeishCLT.MDA
