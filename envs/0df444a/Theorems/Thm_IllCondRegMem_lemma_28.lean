-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_28
-- name    : IllCondRegMem.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:27.222719+00:00
-- url     : https://prove2.me/theorems/5e9b9bfb-ea86-458c-944e-26fd1ef3c323
-- title:
--   Lemma 28 — Gaussian small balls: $\sup_z\mathbb P\{\|Z-z\|\le\varepsilon\}=\mathbb P\{\chi^2_r\le d\varepsilon^2\}\le(ed\varepsilon^2/r)^{r/2}$
-- statement:
--   Let $r,d\ge1$, $\varepsilon\ge0$ and $Z\sim\mathcal N(0,I_r/d)$. Then
--   $$
--   \sup_{z\in\mathbb R^r}\mathbb P\{\|Z-z\|\le\varepsilon\}=\mathbb P\{\chi^2_r\le d\varepsilon^2\}\le\Big(\frac{ed\varepsilon^2}{r}\Big)^{r/2}.
--   $$
--   The supremum is attained at the centre. With $r=d$ and $\varepsilon=1/\sqrt d$ it shows that a learner whose output takes at most $2^M$ values per seed recovers $x^\star$ with probability at most $2^M(e/d)^{d/2}$, the counting bound behind the memory clause of Theorem 1 near $\delta=1$.
--
--   **Formalization Note** $\mathbb P\{\chi^2_r\le u\}$ is written as $\mathbb P\{\|g\|^2\le u\}$ with $g\sim\mathcal N(0,I_r)$.
--
--   Differences from the source:
--   - encoding: χ²_r, Z ∼ N(0, I_r/d), ε → law of ‖g‖² for g ∼ N(0, I_r); multivariateGaussian 0 ((1/d)•I) with d ≥ 1 a natural number; ε ≥ 0; reason: d is the ambient dimension and ε an accuracy radius in the paper
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 28, p.44 (PDF p.45)

import Mathlib
import Definitions.Def_IllCondRegMem_projMat

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- **Lemma 28 (Gaussian small balls).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 28,
p.44: "For Z ∼ N(0, I_r/d), r ≥ 1, sup_{z∈ℝ^r} P{‖Z − z‖ ≤ ε} = P{χ²_r ≤ dε²} ≤ (edε²/r)^{r/2}."

**Formalization Note.** `N(0, I_r/d)` is `multivariateGaussian 0 ((1/d) • I)` on `ℝ^r`;
`P{χ²_r ≤ u}` is written as `P{‖g‖² ≤ u}` for `g ∼ N(0, I_r)`; `d ≥ 1` is the ambient dimension
and `ε ≥ 0` the accuracy radius. -/
theorem lemma_28 (r d : ℕ) (hr : 1 ≤ r) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) :
    (⨆ z : Vec r, multivariateGaussian (0 : Vec r) ((1 / (d : ℝ)) • (1 : Matrix (Fin r) (Fin r) ℝ))
        {x | ‖x - z‖ ≤ ε}) = stdGaussian (Vec r) {g | ‖g‖ ^ 2 ≤ d * ε ^ 2} ∧
    stdGaussian (Vec r) {g | ‖g‖ ^ 2 ≤ d * ε ^ 2} ≤
      ENNReal.ofReal ((Real.exp 1 * d * ε ^ 2 / r) ^ ((r : ℝ) / 2)) := by sorry

end IllCondRegMem
