-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_3
-- name    : LinearSetReconciliation327.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:40.37525+00:00
-- url     : https://prove2.me/theorems/6e0b91e3-f133-4047-aa11-e0b50062d19b
-- title:
--   Lemma 4.3 — Separation by random binary measurements
-- statement:
--   For each $v\in[N]$ let $\beta(v)\in\mathbb F_2^q$ be independent and uniform, with $B(C)=\sum_{v\in C}\beta(v)$. For a fixed $S\subseteq[N]$ and family $\mathcal A$, $\Pr[\exists C\in\mathcal A\setminus\{S\}:B(C)=B(S)]\le|\mathcal A\setminus\{S\}|2^{-q}$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 4.3, PDF p.17 (printed p.16)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 4.3 (Separation by random binary measurements), PDF p.17 (printed p.16). -/
theorem lemma_4_3 (N q : ℕ) (S : Finset (Fin N)) (A : Finset (Finset (Fin N))) :
    prU (fun β : Fin N → Fin q → ZMod 2 =>
        ∃ C ∈ A.erase S, ∑ v ∈ C, β v = ∑ v ∈ S, β v) ≤
      ((A.erase S).card : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by sorry

end LinearSetReconciliation327.Main
