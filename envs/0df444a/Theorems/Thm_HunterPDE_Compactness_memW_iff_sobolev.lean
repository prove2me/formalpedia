-- Prove2me | Theorems.Thm_HunterPDE_Compactness_memW_iff_sobolev
-- name    : HunterPDE.Compactness.memW_iff_sobolev
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T09:12:20.384626+00:00
-- url     : https://prove2.me/theorems/1eb5b821-f5a6-444f-8bf0-046966852462
-- title:
--   Equivalence of the two distributional Sobolev membership presentations
-- statement:
--   For every subset $\Omega\subseteq\mathbb R^n$, every order $k\ge0$, exponent $p\in[0,\infty]$, and real function $f$, the Compactness and Sobolev chapter predicates for $f\in W^{k,p}(\Omega)$ are equivalent. No openness or positive dimension assumption is needed.
--
--   The Compactness definition quantifies over a finite set of multi-indices and uses a flattened word of coordinate derivatives. The Sobolev definition quantifies over all multi-indices of total order at most $k$, iterates each coordinate derivative, and separately asks that $f$ be locally integrable. The zero multi-index supplies this local integrability in the first presentation. Flattening the derivative word and bounding each coordinate of a multi-index by its total degree identify the remaining clauses.
-- source:
--   Hunter, Notes on Partial Differential Equations, Definition 3.2, pp. 47-48, and Definition 3.23, p. 58, https://math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . Equivalence of two formal presentations of these definitions.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.memW_iff_sobolev {n k : ℕ} {p : ℝ≥0∞}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    HunterPDE.Compactness.MemW k p Ω f ↔ HunterPDE.Sobolev.MemW k p Ω f := by sorry
