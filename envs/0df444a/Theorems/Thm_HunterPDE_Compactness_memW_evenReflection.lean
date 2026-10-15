-- Prove2me | Theorems.Thm_HunterPDE_Compactness_memW_evenReflection
-- name    : HunterPDE.Compactness.memW_evenReflection
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-15T08:36:28.680345+00:00
-- url     : https://prove2.me/theorems/7cc95f3e-8fe7-4997-b1d3-255ac9827bf2
-- title:
--   Even reflection preserves first-order Sobolev membership, including p = infinity
-- statement:
--   Let $H=\{x\in\mathbb R^{m+1}:x_{m+1}>0\}$ and let $1\le p\le\infty$. Define $R(x',t)=(x',|t|)$ and $Ef=f\circ R$. Then
--   $$f\in W^{1,p}(H)\quad\Longrightarrow\quad Ef\in W^{1,p}(\mathbb R^{m+1}).$$
--
--   This is the weak differentiability part of the reflection construction suggested before Hunter's Theorem 3.41. The tangential weak derivatives reflect evenly, while the normal weak derivative reflects oddly. In particular the gluing across the boundary creates no distribution supported on the boundary. The hypotheses control integrability up to the boundary; merely knowing local weak differentiability inside the open half-space would not suffice. The endpoint $p=\infty$ is included and must not be deduced from finite-p norm density.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), §3.9, pp. 71–72, reflection construction preceding Theorem 3.41. https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . This is an auxiliary lemma for the indicated construction, not a separately numbered assertion in the source.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.memW_evenReflection (m : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : HunterPDE.Compactness.MemW 1 p (HunterPDE.Compactness.upperHalfSpace m) f) :
    HunterPDE.Compactness.MemW 1 p Set.univ (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      f (WithLp.toLp 2 (fun i => if i = Fin.last m then |x i| else x i))) := by sorry
