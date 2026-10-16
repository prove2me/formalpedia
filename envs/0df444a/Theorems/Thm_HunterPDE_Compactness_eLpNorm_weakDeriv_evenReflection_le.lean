-- Prove2me | Theorems.Thm_HunterPDE_Compactness_eLpNorm_weakDeriv_evenReflection_le
-- name    : HunterPDE.Compactness.eLpNorm_weakDeriv_evenReflection_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T08:36:32.145914+00:00
-- url     : https://prove2.me/theorems/aaaa6d73-2add-421c-a483-929202c4ddf3
-- title:
--   Componentwise Lp estimate for the weak derivatives of even reflection
-- statement:
--   Let $1\le p\le\infty$, $f\in W^{1,p}(H)$, where $H$ is the upper half-space in $\mathbb R^{m+1}$, and let $Ef(x',t)=f(x',|t|)$. For every multi-index $\alpha$ with $|\alpha|\le1$,
--   $$\|\partial^\alpha Ef\|_{L^p(\mathbb R^{m+1})}\le2\|\partial^\alpha f\|_{L^p(H)}.$$
--
--   Here the derivatives are the chosen representatives of the distributional derivatives, and the assertion includes the zero-order term. This is the componentwise estimate in the reflection construction for Hunter's Theorem 3.41. Reflection preserves Lebesgue measure, so the sharper factor is $2^{1/p}$ for finite $p$, and $1$ at infinity; the stated factor $2$ is a convenient uniform bound. Identifying the chosen derivatives requires weak derivative uniqueness and the even tangential/odd normal reflection identities, not just a change of variables applied to an arbitrary function.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), §3.9, pp. 71–72, reflection construction preceding Theorem 3.41. https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . This is an auxiliary lemma for the indicated construction, not a separately numbered assertion in the source.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.eLpNorm_weakDeriv_evenReflection_le (m : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : HunterPDE.Compactness.MemW 1 p (HunterPDE.Compactness.upperHalfSpace m) f)
    (α : Fin (m + 1) → ℕ)
    (hα : α ∈ HunterPDE.Compactness.multiIndicesLe (m + 1) 1) :
    eLpNorm (HunterPDE.Shared.weakDeriv Set.univ α (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      f (WithLp.toLp 2 (fun i => if i = Fin.last m then |x i| else x i)))) p (volume.restrict Set.univ) ≤
      2 * eLpNorm (HunterPDE.Shared.weakDeriv (HunterPDE.Compactness.upperHalfSpace m) α f)
        p (volume.restrict (HunterPDE.Compactness.upperHalfSpace m)) := by sorry
