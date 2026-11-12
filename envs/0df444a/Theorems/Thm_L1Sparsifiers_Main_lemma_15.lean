-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_lemma_15
-- name    : L1Sparsifiers.Main.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:23.253829+00:00
-- url     : https://prove2.me/theorems/6237c122-5337-496f-802a-f75b80a39d4a
-- title:
--   Lemma 15 — the erosion volume $s\mapsto\mathrm{Vol}_n(K\ominus s[-v,v])$ is convex
-- statement:
--   Let $K\subseteq\mathbb R^n$ be a compact convex set (possibly empty) and $v\in\mathbb R^n$ (possibly $0$). Then the function
--   $$f(s)=\mathrm{Vol}_n\big(K\ominus s[-v,v]\big)$$
--   is convex on $\mathbb R_{\ge0}$. Here $s[-v,v]$ is the closed segment from $-sv$ to $sv$ and $\ominus$ is Minkowski subtraction.
--
--   Lemma 16 extends this from one segment to zonotopes, coordinate by coordinate.
--
--   Differences from the source:
--   - encoding: Lebesgue volume Vol (a value in [0,∞]) → (volume ·).toReal; reason: every set measured here is bounded, so its volume is finite and toReal is the same number
--   - encoding: s[−v,v] for s ≥ 0 → segment ℝ (−(s•v)) (s•v); reason: the same closed segment
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §3.1, Lemma 15, p.8

import Mathlib
import Definitions.Def_L1Sparsifiers_Main_Zonotope

namespace L1Sparsifiers.Main

open MeasureTheory

/-- **Lemma 15** (p.8). "Let K ⊆ ℝⁿ be a compact convex set and let v ∈ ℝⁿ. Let
f(s) := Volₙ(K ⊖ s[−v, v]). Then the function f is convex on ℝ_{≥0}."

`s[−v, v]` is the closed segment from `−s v` to `s v`; `K` may be empty and `v` may be `0`. The
erosion lies inside the compact `K` (the segment contains `0`), so its volume is finite and is
taken as a real number. -/
theorem lemma_15 {n : ℕ} (K : Set (Fin n → ℝ)) (hKc : IsCompact K) (hKcv : Convex ℝ K)
    (v : Fin n → ℝ) :
    ConvexOn ℝ (Set.Ici (0 : ℝ))
      (fun s : ℝ => (volume (minkowskiSub K (segment ℝ (-(s • v)) (s • v)))).toReal) := by sorry

end L1Sparsifiers.Main
