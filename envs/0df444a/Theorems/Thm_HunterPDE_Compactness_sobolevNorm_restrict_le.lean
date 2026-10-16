-- Prove2me | Theorems.Thm_HunterPDE_Compactness_sobolevNorm_restrict_le
-- name    : HunterPDE.Compactness.sobolevNorm_restrict_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T08:38:55.82325+00:00
-- url     : https://prove2.me/theorems/4fdeae98-36d3-4b16-a4da-3bee4b516429
-- title:
--   Restriction contracts the Sobolev norm, independently of representatives
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be open, $k\in\mathbb N_0$, and $p\in[0,\infty]$. Suppose $F\in W^{k,p}(\mathbb R^n)$ and $f=F$ almost everywhere on $\Omega$. Then
--   $$\|f\|_{W^{k,p}(\Omega)}\le\|F\|_{W^{k,p}(\mathbb R^n)}.$$
--
--   For $p<1$ the displayed expression is the same derivative-based functional, without claiming the norm axioms. This restriction estimate lets whole-space approximation estimates descend to arbitrary open sets and is invariant under changes on null sets.
--
--   **Formalization Note.** The left expression uses the Compactness chapter's norm and the right expression the Sobolev chapter's norm. Thus the assertion also reconciles their multi-index enumerations and their chosen weak-derivative representatives.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), Definition 3.2, pp. 47–48, Definition 3.23, p. 58, and the restriction step preceding Theorem 3.42, p. 72, https://math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . Auxiliary consequence of those definitions, generalized from the half-space to any open subset.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.sobolevNorm_restrict_le {n k : ℕ} {p : ℝ≥0∞}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : HunterPDE.Sobolev.MemW k p Set.univ F)
    (h : f =ᵐ[volume.restrict Ω] F) :
    HunterPDE.Compactness.sobolevNorm k p Ω f ≤
      HunterPDE.Sobolev.sobolevNorm k p Set.univ F := by sorry
