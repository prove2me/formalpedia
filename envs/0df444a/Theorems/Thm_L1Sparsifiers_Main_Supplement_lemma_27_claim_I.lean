-- Prove2me | Theorems.Thm_L1Sparsifiers_Main_Supplement_lemma_27_claim_I
-- name    : L1Sparsifiers.Main.Supplement.lemma_27_claim_I
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:17:45.466447+00:00
-- url     : https://prove2.me/theorems/d96073b8-0062-4c7d-96a2-682f0cf8d0c8
-- title:
--   §7, proof of Lemma 27, Claim I — $s\mapsto\det_+(B-sA)$ is convex on $\mathbb R$
-- statement:
--   Let $A,B\in\mathbb R^{n\times n}$ be symmetric matrices with $A\succeq0$ ($B$ arbitrary symmetric). Then the function
--   $$f:\mathbb R\to\mathbb R_{\ge0},\qquad f(s)=\det\nolimits_+(B-sA),$$
--   is convex on the whole real line, where $\det_+(M)=\det M$ if $M\succeq0$ and $0$ otherwise.
--
--   This is the univariate case of Lemma 27: a real-rooted polynomial is convex up to its smallest root, and $f$ vanishes beyond it.
--
--   Differences from the source:
--   - encoding: A, B symmetric with A ⪰ 0; f : ℝ → ℝ_{≥0} convex → A.PosSemidef (which includes symmetry), B.IsSymm; ConvexOn ℝ Set.univ (fun s => detPlus (B − s • A)); reason: the same hypotheses; the codomain ℝ_{≥0} is a property of det₊, not an assumption
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §7, proof of Lemma 27, Claim I, p.18

import Mathlib
import Definitions.Def_L1Sparsifiers_Main_Supplement_DetPlus

namespace L1Sparsifiers.Main.Supplement

/-- **§7, proof of Lemma 27, Claim I** (Reis–Rothvoss, STOC 2027 submission #162, p.18).
"Let A, B ∈ ℝ^{n×n} symmetric matrices with A ⪰ 0. Then the function f : ℝ → ℝ_{≥0} with
f(s) := det₊(B − sA) is convex."

`A ⪰ 0` is `Matrix.PosSemidef` (which includes symmetry); `B` is an arbitrary symmetric matrix (not
assumed positive semidefinite). Convexity is on the whole real line. -/
theorem lemma_27_claim_I {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef)
    (hB : B.IsSymm) :
    ConvexOn ℝ Set.univ (fun s : ℝ => detPlus (B - s • A)) := by sorry

end L1Sparsifiers.Main.Supplement
