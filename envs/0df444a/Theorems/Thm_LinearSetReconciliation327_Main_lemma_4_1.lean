-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_1
-- name    : LinearSetReconciliation327.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:41.409797+00:00
-- url     : https://prove2.me/theorems/64616e85-2370-4fb9-b86c-79425af7645d
-- title:
--   Lemma 4.1 — Hypergeometric tail
-- statement:
--   Let $S$ be a uniform $K$-subset of $[N]$, $I\subseteq[N]$, $Z=|S\cap I|$ and $\mu=K|I|/N>0$. For all $t\ge0$, $\Pr[Z\ge\mu+t]\le\exp(-t^2/(2(\mu+t)))$, and for all $k\ge2\mu$, $\Pr[Z\ge k]\le e^{-k/8}$.
--
--   Differences from the source:
--   - encoding: 0-based or 1-based coordinates [N] → 0-based Fin N or range N, with supports as finite sets and vector addition as symmetric difference; reason: the source identifies subsets with characteristic vectors and any injection relabels the coordinates
--   - generalization: k in the claim for k ≥ 2µ (integer in its uses) → every real k ≥ 2µ; reason: integer k is a special case and the same argument applies
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 4.1, PDF p.16 (printed p.15)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

open Classical in
/-- Lemma 4.1 (Chernoff bound for hypergeometric random variables), PDF p.16 (printed p.15). `S` is
uniform among the `K`-subsets of `[N]`. -/
theorem lemma_4_1 (N K : ℕ) (hK : K ≤ N) (I : Finset (Fin N))
    (hμ : 0 < (K : ℝ) * I.card / N) :
    let μ : ℝ := (K : ℝ) * I.card / N
    let Pr : (Finset (Fin N) → Prop) → ℝ := fun E =>
      (((powersetCard K (univ : Finset (Fin N))).filter E).card : ℝ) /
        ((powersetCard K (univ : Finset (Fin N))).card : ℝ)
    (∀ t : ℝ, 0 ≤ t →
      Pr (fun S => μ + t ≤ ((S ∩ I).card : ℝ)) ≤ Real.exp (-(t ^ 2 / (2 * (μ + t))))) ∧
    (∀ k : ℝ, 2 * μ ≤ k → Pr (fun S => k ≤ ((S ∩ I).card : ℝ)) ≤ Real.exp (-(k / 8))) := by sorry

end LinearSetReconciliation327.Main
