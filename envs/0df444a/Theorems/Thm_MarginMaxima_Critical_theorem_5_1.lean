-- Prove2me | Theorems.Thm_MarginMaxima_Critical_theorem_5_1
-- name    : MarginMaxima.Critical.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:03:19.487984+00:00
-- url     : https://prove2.me/theorems/12a539e7-15ac-414a-b0f4-8dc545f1a466
-- title:
--   Theorem 5.1 — the Reed–Solomon gadget: for $r\ge R(q,k)$, block systems with parameters $(g^0,0,\kappa)$ and $(g^w,\pi,0)$ realize $r\ln r/(4826(k+2))$ documents with $r$ heads
-- statement:
--   Let $q\ge3$ be a prime power, $k\ge4$ an integer and $R(q,k)=\exp(9(k+2)(2k+5)q^{2k+10}\ln q)$. There is an absolute $C$ such that for $r\ge R(q,k)$, with $m=r\ln r/(4826(k+2))$:
--
--   - a block system with parameters $(g^0,0,\kappa)$, $\kappa^2=\pi/(1+\pi)$, has a set of at least $m$ documents realized by $r$ heads, and so does a block system with parameters $(g^w,\pi,0)$;
--   - in both cases the heads used for all labels and the documents number at most $r^{C(k+2)}$ in total;
--   - consequently, for $d\ge m$, $\mathrm{fat}_{g^w}(F^{(d)}_{\max,r})\ge m$ and $\mathrm{fat}^0_{g^0}(F^{(d)}_{\max,r})\ge m$.
--
--   Differences from the source:
--   - reading: 'A block system with parameters (g⁰, 0, κ) has a set of at least m documents realized by r heads' → existence of a block system with these parameters and of such a set; reason: the paper constructs one (the Reed–Solomon line system); a universal reading is false for trivial systems
--   - encoding: the block system's Hilbert space, documents and blocks → EuclideanSpace ℝ (Fin D), Fin n, Fin nb for some D, n, nb; reason: finitely many documents and block vectors span a finite-dimensional space, isometric to some ℝ^D; finite sets are equivalent to Fin n
--   - reading: the heads used for all labels and the documents number at most r^{C(k+2)} in total → a finite set Hs of ℒ-parts containing every head of every labelling (RealizesWith Y r (· ∈ Hs)) with n + |Hs| ≤ r^{C(k+2)}; reason: heads + all documents of the system, as counted in the proof (p. 12)
--   - encoding: C absolute; q a prime power; κ² = π/(1 + π) → ∃ Cabs : ℝ before q, k, r; IsPrimePow q; κ = √(π/(1 + π)); reason: κ ≥ 0 in Definition 4.1
--   - encoding: fat_{g^w}(F^(d)_max,r) ≥ m and fat⁰_{g^0}(F^(d)_max,r) ≥ m for d ≥ m, fat an integer or ∞ → ENNReal.ofReal m ≤ (fat (MaxClass d r) (gwRS q k) : ℝ≥0∞) and ENNReal.ofReal m ≤ (fat0 (MaxClass d r) (g0RS q k) : ℝ≥0∞) for every d : ℕ with m ≤ d; reason: fat is ℕ∞-valued in the fixed dimension d (no supremum over d here); ofReal of the positive real m is exact
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 9, Theorem 5.1

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_MarginMaxima_Critical_MaxClass
import Definitions.Def_MarginMaxima_Critical_BlockSystem
import Definitions.Def_MarginMaxima_Critical_ReedSolomon

open BartlettNN.Margin
open scoped ENNReal

namespace MarginMaxima.Critical

theorem theorem_5_1 :
    ∃ Cabs : ℝ, ∀ q k : ℕ, IsPrimePow q → 3 ≤ q → 4 ≤ k → ∀ r : ℕ, RqK q k ≤ r →
      (∃ (D n nb : ℕ) (S : BlockSystem (EuclideanSpace ℝ (Fin D)) (Fin n) (Fin nb) (g0RS q k) 0
            (Real.sqrt (piRS q k / (1 + piRS q k))))
          (Y : Finset (Fin n)) (Hs : Finset (EuclideanSpace ℝ (Fin D))),
          (r : ℝ) * Real.log r / (4826 * (k + 2)) ≤ Y.card ∧ S.RealizesWith Y r (· ∈ Hs) ∧
          (n : ℝ) + Hs.card ≤ (r : ℝ) ^ (Cabs * (k + 2))) ∧
      (∃ (D n nb : ℕ) (S : BlockSystem (EuclideanSpace ℝ (Fin D)) (Fin n) (Fin nb) (gwRS q k)
            (piRS q k) 0)
          (Y : Finset (Fin n)) (Hs : Finset (EuclideanSpace ℝ (Fin D))),
          (r : ℝ) * Real.log r / (4826 * (k + 2)) ≤ Y.card ∧ S.RealizesWith Y r (· ∈ Hs) ∧
          (n : ℝ) + Hs.card ≤ (r : ℝ) ^ (Cabs * (k + 2))) ∧
      (∀ d : ℕ, (r : ℝ) * Real.log r / (4826 * (k + 2)) ≤ d →
        ENNReal.ofReal ((r : ℝ) * Real.log r / (4826 * (k + 2))) ≤
            (fat (MaxClass d r) (gwRS q k) : ℝ≥0∞) ∧
          ENNReal.ofReal ((r : ℝ) * Real.log r / (4826 * (k + 2))) ≤
            (fat0 (MaxClass d r) (g0RS q k) : ℝ≥0∞)) := by sorry

end MarginMaxima.Critical
