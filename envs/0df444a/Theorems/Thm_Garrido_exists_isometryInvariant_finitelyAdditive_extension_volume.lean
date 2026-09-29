-- Prove2me | Theorems.Thm_Garrido_exists_isometryInvariant_finitelyAdditive_extension_volume
-- name    : Garrido.exists_isometryInvariant_finitelyAdditive_extension_volume
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:34:37.185479+00:00
-- url     : https://prove2.me/theorems/a45a572b-951e-4c4b-b0c2-3058f1427c68
-- title:
--   Corollary 2.5 — Lebesgue measure extends invariantly in dimensions 1 and 2
-- statement:
--   For every natural number $n \le 2$ there is a function
--   $m : \mathcal{P}(\mathbb{R}^n) \to [0,\infty]$ on **all** subsets of Euclidean $n$-space which
--   is
--
--   - a finitely additive measure: $m(\emptyset) = 0$ and $m(s \cup t) = m(s) + m(t)$ for disjoint
--     $s, t$;
--   - invariant under every isometry $f$ of $\mathbb{R}^n$: $m(f(s)) = m(s)$;
--   - an extension of Lebesgue measure: $m(s) = \operatorname{vol}(s)$ for every
--     **Lebesgue-measurable** $s$.
--
--   The measurability condition is null-measurability with respect to volume, that is Lebesgue
--   measurability, rather than Borel measurability. The distinction matters and is easy to
--   over-read: on $\mathbb{R}^n$ Mathlib's `MeasurableSet` is the Borel $\sigma$-algebra, which is
--   strictly smaller, and agreement on Borel sets alone would not give agreement on all
--   Lebesgue-measurable sets for a merely finitely additive $m$. The source's corollary is about
--   extending Lebesgue measure, so Lebesgue measurability is what is asserted.
--
--   The cases $n = 0, 1, 2$ are all included. The statement is the positive assertion — the
--   existence of the invariant extension — from which the source draws the negative conclusion that
--   no paradoxical decomposition of $\mathbb{R}^1$ or $\mathbb{R}^2$ can exist; the
--   non-existence itself is not what is asserted here.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, Corollary 2.5. The source states the corollary in the negative form "The Banach–Tarski paradox has no analogue for dimensions 1 and 2" and proves it by exhibiting the invariant extension; the invariant extension is what is formalised here; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability
open scoped ENNReal

namespace Garrido

theorem exists_isometryInvariant_finitelyAdditive_extension_volume (n : ℕ) (hn : n ≤ 2) :
    ∃ m : Set (EuclideanSpace ℝ (Fin n)) → ℝ≥0∞,
      IsFinitelyAdditiveMeasure m ∧
      (∀ (f : EuclideanSpace ℝ (Fin n) ≃ᵢ EuclideanSpace ℝ (Fin n))
        (s : Set (EuclideanSpace ℝ (Fin n))), m (f '' s) = m s) ∧
      (∀ s : Set (EuclideanSpace ℝ (Fin n)),
        MeasureTheory.NullMeasurableSet s MeasureTheory.volume →
          m s = MeasureTheory.volume s) := by
  sorry

end Garrido
