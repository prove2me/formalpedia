-- Prove2me | Theorems.Thm_NoStretch1PRS_lemma_3_7
-- name    : NoStretch1PRS.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:23.134452+00:00
-- url     : https://prove2.me/theorems/db0ba0d8-9bd6-4f06-b54e-a6f355f019a1
-- title:
--   Lemma 3.7 — Lévy's lemma
-- statement:
--   Let $d\in\mathbb N$ and let $f:S^d\to\mathbb R$ be $L$-Lipschitz for the Euclidean distance on the unit sphere $S^d\subset\mathbb R^{d+1}$, $L>0$. Then for every $\varepsilon>0$,
--
--   $$\Pr_{x\sim S^d}\Big[\big|f(x)-\mathop{\mathbb E}_{z\sim S^d}f(z)\big|\ge\varepsilon\Big]\le4\exp\Big(-\frac{d\varepsilon^2}{9\pi^3L^2}\Big),$$
--
--   where $x\sim S^d$ is uniform on $S^d$.
--
--   Concentration of measure on the sphere turns the averaged bound of Theorem 5.1 into a bound for almost every CHRS family.
--
--   Differences from the source:
--
--   - encoding: f L-Lipschitz (L ≥ 0) → L > 0; reason: the printed bound divides by L² and is undefined at L = 0
-- source:
--   Chen, Coladangelo, Lin, Skoumios, Tysdal, Wang, No linear stretching of single-copy quantum pseudorandomness, arXiv:2606.24736 (held version, sha256 2670cb2f…), Lemma 3.7, p.18 (cited from [Led01]); S^d, p.15

import Mathlib
import Definitions.Def_NoStretch1PRS_sphereMeasure

set_option autoImplicit false

namespace NoStretch1PRS

open MeasureTheory

/-- **Lemma 3.7 (Lévy's lemma).**
B. Chen, A. Coladangelo, Y.-T. Lin, N. Skoumios, J. Tysdal, Y. Wang, *No linear stretching of
single-copy quantum pseudorandomness*, arXiv:2606.24736 (held version, sha256 2670cb2f…), Lemma 3.7, p.18 (cited from [Led01]).

Let `d ∈ ℕ` and `f : S^d → ℝ` be `L`-Lipschitz for the Euclidean distance on the unit sphere
`S^d ⊂ ℝ^{d+1}`. Then for every `ε > 0`,
`Pr_{x∼S^d}[|f(x) − E_{z∼S^d} f(z)| ≥ ε] ≤ 4 exp(−dε²/(9π³L²))`, with `x` uniform on `S^d`.

**Formalization Note.** `S^d` is the unit sphere of `ℝ^{d+1}` (§3, p.15: "the `d`-dimensional
sphere") with the uniform probability measure `sphereMeasure (Fin (d+1))`. The bound is stated for
`L > 0`, where the printed formula is defined. -/
theorem lemma_3_7 (d : ℕ) (L : ℝ) (hL : 0 < L) (f : Sph (Fin (d + 1)) → ℝ)
    (hf : ∀ x y : Sph (Fin (d + 1)), |f x - f y| ≤ L * dist x y) (ε : ℝ) (hε : 0 < ε) :
    (sphereMeasure (Fin (d + 1))).real
        {x | ε ≤ |f x - ∫ z, f z ∂(sphereMeasure (Fin (d + 1)))|} ≤
      4 * Real.exp (-((d : ℝ) * ε ^ 2) / (9 * Real.pi ^ 3 * L ^ 2)) := by sorry

end NoStretch1PRS
