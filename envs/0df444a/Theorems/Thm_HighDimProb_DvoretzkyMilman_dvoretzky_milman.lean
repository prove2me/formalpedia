-- Prove2me | Theorems.Thm_HighDimProb_DvoretzkyMilman_dvoretzky_milman
-- name    : HighDimProb.DvoretzkyMilman.dvoretzky_milman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:14:03.48998+00:00
-- url     : https://prove2.me/theorems/41ec871d-4337-4927-a407-e1d5304646a6
-- title:
--   Theorem 11.3.3 — Dvoretzky-Milman's theorem (Gaussian form)
-- statement:
--   This is **Dvoretzky-Milman's theorem**, the book's own closing theorem and the capstone the
--   whole book builds toward: a random Gaussian projection of a high-dimensional set is, with high
--   probability, almost a round ball — quantitatively, the convex hull of the image of a bounded
--   set $T$ under a Gaussian random matrix sandwiches between two concentric Euclidean balls whose
--   radii differ by only a factor of $1\pm\varepsilon$, as soon as the number of measurements
--   exceeds (a constant times) the stable dimension of $T$.
--
--   Let $A$ be an $m\times n$ Gaussian random matrix with i.i.d. $N(0,1)$ entries, $T\subseteq
--   \mathbb R^n$ a bounded set containing the origin, and $\varepsilon\in(0,1)$. Suppose
--   $m\le c\varepsilon^2d(T)$, where $d(T)$ is the stable dimension of $T$. Then with probability
--   at least $0.99$,
--   $$
--   (1-\varepsilon)B \;\subseteq\; \mathrm{conv}(AT) \;\subseteq\; (1+\varepsilon)B,
--   $$
--   where $B$ is the Euclidean ball of radius $w(T)$ centered at the origin.
--
--   **Formalization Note** $A$ is `Ω → Matrix (Fin m) (Fin n) ℝ` with `IsGaussianMatrix P A`.
--   $d(T)$ is `StableDimension w diam` for explicit real witnesses of `GaussianWidth T` and
--   `Metric.diam T` (see `StableDimension`'s own note on the $w$-vs-$h$-based formalization
--   choice). $\mathrm{conv}(AT)$ is `convexHull ℝ` of the image of $T$ under $A$'s `mulVec`. The
--   book's own proof reduces the general case to $T$ containing the origin by translation
--   ("Translating $T$ if necessary, we can assume that $T$ contains the origin"; Remark 11.3.4);
--   this formalization states that WLOG-reduced case directly, adding $0\in T$ as an explicit
--   hypothesis rather than formalizing the translation step itself — a disclosed deviation from
--   the literal, untranslated printed statement, recorded in `STATUS.md`.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 276, Theorem 11.3.3

import Mathlib
import Definitions.Def_HighDimProb_DvoretzkyMilman_ExpSup
import Definitions.Def_HighDimProb_DvoretzkyMilman_GaussianWidth
import Definitions.Def_HighDimProb_DvoretzkyMilman_StableDimension
import Definitions.Def_HighDimProb_DvoretzkyMilman_IsGaussianMatrix

open MeasureTheory ProbabilityTheory

namespace HighDimProb.DvoretzkyMilman

/-- **Theorem 11.3.3** (Dvoretzky-Milman's theorem: Gaussian form), Vershynin, *High-Dimensional
Probability* (2018), p. 276 (PDF p. 284) — the book's own closing theorem.

"Let `A` be an `m × n` Gaussian random matrix with i.i.d. `N(0, 1)` entries, `T ⊂ ℝⁿ` be a bounded
set, and let `ε ∈ (0,1)`. Suppose `m ≤ cε²d(T)` where `d(T)` is the stable dimension of `T`
introduced in Section 7.6. Then with probability at least `0.99`, we have `(1−ε)B ⊂ conv(AT) ⊂
(1+ε)B` where `B` is a Euclidean ball with radius `w(T)`."

`A` is `Ω → Matrix (Fin m) (Fin n) ℝ` with `IsGaussianMatrix P A` (reused per rule, this chunk's
own copy since `08-matrix-deviation`'s analogous machinery is a still-draft definition). `d(T)` is
`stableDimension w diam` for explicit real witnesses `w`/`diam` of `gaussianWidth T`/`Metric.diam
T` respectively — see `Def_HighDimProb_DvoretzkyMilman_StableDimension.lean` for the disclosed
`w`-vs-`h`-based formalization choice. `conv(AT)` is `convexHull ℝ (image of T under
Matrix.mulVec ∘ A ω)`.

**Ball center**: the book's own proof opens "Translating `T` if necessary, we can assume that `T`
contains the origin," and Remark 11.3.4 confirms the ball `B` is then centered at the origin
(otherwise at an arbitrary fixed point of `T`). This formalization adds `(0 : EuclideanSpace ℝ
(Fin n)) ∈ T` as an explicit hypothesis rather than the fully general (translated) statement, i.e.
states the WLOG-reduced case the book's own proof reduces every case to — disclosed in
`STATUS.md`/`MODERATION_NOTES.md` as a deviation from the literal printed theorem (which has no
such hypothesis, only the surrounding proof's reduction), made for tractability; the general case
follows from this one by the same translation argument the book's own proof performs, and is not
formalized here. -/
theorem dvoretzky_milman :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (A : Ω → Matrix (Fin m) (Fin n) ℝ),
        IsGaussianMatrix P A →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))), Bornology.IsBounded T →
        (0 : EuclideanSpace ℝ (Fin n)) ∈ T →
        ∀ (ε : ℝ), 0 < ε → ε < 1 →
        ∀ (w : ℝ), gaussianWidth T = (w : EReal) →
        (m : ℝ) ≤ c * ε ^ 2 * stableDimension w (Metric.diam T) →
        (99 / 100 : ENNReal) ≤
          P {ω |
            Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ((1 - ε) * w) ⊆
                convexHull ℝ ((fun x : EuclideanSpace ℝ (Fin n) =>
                  (EuclideanSpace.equiv (Fin m) ℝ).symm ((A ω).mulVec x)) '' T) ∧
              convexHull ℝ ((fun x : EuclideanSpace ℝ (Fin n) =>
                  (EuclideanSpace.equiv (Fin m) ℝ).symm ((A ω).mulVec x)) '' T) ⊆
                Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) ((1 + ε) * w)} := by sorry

end HighDimProb.DvoretzkyMilman
