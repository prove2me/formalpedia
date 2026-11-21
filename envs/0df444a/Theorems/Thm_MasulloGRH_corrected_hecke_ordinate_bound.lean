-- Prove2me | Theorems.Thm_MasulloGRH_corrected_hecke_ordinate_bound
-- name    : MasulloGRH.corrected_hecke_ordinate_bound
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:04:25.337056+00:00
-- url     : https://prove2.me/theorems/fef717f9-afda-4617-9c6f-3213ccc44db7
-- title:
--   Corrected Hecke Euler-factor bound on signed ordinates, uniformly on horizontal lines
-- statement:
--   Let $F$ be a number field and $S_f$ a finite set of its finite places. There exists $N>0$, depending only on $S_f$, such that for every unitary Hecke character $\chi$ unramified at $S_f$ there are nondecreasing real ordinates $T_k\in[k,k+1]$ indexed by the integers. They satisfy $T_k\ge0$ for $k\ge0$, $T_k\le0$ for $k<0$, and $|T_k|\to\infty$ as $|k|\to\infty$. If $q_v$ is the residue cardinality and $\pi_v$ a uniformizer, then for every integer $k$ and real $\sigma$,
--   $$
--   1\le N\prod_{v\in S_f}\left|1-\chi_v(\pi_v)q_v^{-(\sigma+iT_k)}\right|.
--   $$
--   This corrects the overlapping sign conditions at $k=0$ in Masullo's Proposition B.5.3.2 and gives the all-real-part bound used for horizontal contours in Lemma 7.1.1.1. It uses the finite-place Euler factors from the mission's Hecke definitions.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes (frozen 20 November 2026), Proposition B.5.3.2 and Lemma 7.1.1.1. Corrected arithmetic successor of Prove2Me 43cd773f-c20d-48e7-b651-b5d9249d5fe2. The finite sampling theorem is a09f5fc7-520f-4b39-a866-734d8d92cce1.

import Definitions.Def_MasulloGRH_IdeleNorm
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

open NumberField IsDedekindDomain MasulloGRH

theorem MasulloGRH.corrected_hecke_ordinate_bound
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ N : ℝ, 0 < N ∧ ∀ (χ : HeckeCharacter F), (∀ v ∈ Sf, χ.IsUnramifiedAt v) →
      ∃ T : ℤ → ℝ, (∀ k : ℤ, T k ∈ Set.Icc (k : ℝ) ((k : ℝ) + 1)) ∧
        (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
        (∀ k, T k ≤ T (k+1)) ∧
        Filter.Tendsto (fun k => |T k|) Filter.cofinite Filter.atTop ∧
        ∀ k (σ : ℝ), 1 ≤ N * ∏ v ∈ Sf, ‖eulerFactorInv χ v ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ := by sorry
