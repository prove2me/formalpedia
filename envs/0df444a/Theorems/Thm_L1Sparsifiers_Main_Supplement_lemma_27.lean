-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_Supplement_lemma_27
-- name    : L1Sparsifiers.Main.Supplement.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:18:17.216208+00:00
-- url     : https://prove2.me/theorems/0d4fdcc7-6535-410d-8aca-ce500dbd60cc
-- title:
--   Lemma 27 — $\Phi(t)=\det_+(B-\sum_i t_iA_i)$ is separately convex on $\mathbb R^m$
-- statement:
--   Let $A_1,\dots,A_m\in\mathbb R^{n\times n}$ be positive semidefinite and let $B\in\mathbb R^{n\times n}$ be symmetric. Define $\Phi:\mathbb R^m\to\mathbb R_{\ge0}$ by
--   $$\Phi(t)=\det\nolimits_+\Big(B-\sum_{i=1}^m t_iA_i\Big).$$
--   Then $\Phi$ is separately convex on all of $\mathbb R^m$: for every $t\in\mathbb R^m$ and every coordinate $j$, the function $u\mapsto\Phi(t_1,\dots,t_{j-1},u,t_{j+1},\dots,t_m)$ is convex on $\mathbb R$.
--
--   It is the spectral counterpart of Lemma 16 and feeds the positivity bound of Lemma 18 in the proof of Theorem 29.
--
--   Differences from the source:
--   - encoding: Φ : ℝ^m → ℝ_{≥0} separately convex → SepConvexOn Set.univ (fun t => detPlus (B − ∑ i, t i • A i)) with the published SepConvexOn; reason: separate convexity on Ω^m with Ω = ℝ is exactly the published definition at Ω = Set.univ
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §7, Lemma 27, p.18

import Mathlib
import Definitions.Def_L1Sparsifiers_Main_SeparatelyConvex
import Definitions.Def_L1Sparsifiers_Main_Supplement_DetPlus

namespace L1Sparsifiers.Main.Supplement

/-- **Lemma 27** (Reis–Rothvoss, STOC 2027 submission #162, §7, p.18).
"Let A₁, …, A_m ⪰ 0 and B symmetric. Define a function Φ : ℝ^m → ℝ_{≥0} by
Φ(t) := det₊(B − ∑_{i=1}^m tᵢ Aᵢ). Then Φ is separately convex."

All matrices are real `n × n`; `Aᵢ ⪰ 0` is `Matrix.PosSemidef`; `B` is any symmetric matrix.
Separate convexity (`SepConvexOn`) is on all of `ℝ^m` (`Ω = ℝ`). -/
theorem lemma_27 {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).PosSemidef)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    L1Sparsifiers.Main.SepConvexOn Set.univ
      (fun t : Fin m → ℝ => detPlus (B - ∑ i, t i • A i)) := by sorry

end L1Sparsifiers.Main.Supplement
