-- Prove2me | Theorems.Thm_HunterPDE_Shared_integral_evenReflection_mul_testFunction
-- name    : HunterPDE.Shared.integral_evenReflection_mul_testFunction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T17:46:23.400403+00:00
-- url     : https://prove2.me/theorems/f04f9111-81c5-4425-af75-f0073df24e5f
-- title:
--   Weak integration by parts for even reflection across a half-space boundary
-- statement:
--   Let $H=\{(x',t):t>0\}$, let $1\le p\le\infty$, and suppose $f,g\in L^p(H)$ with $g=\partial_i f$ weakly on $H$. Put $Ef(x',t)=f(x',|t|)$ and define
--   $$G_i(x',t)=\begin{cases}-g(x',|t|),&i=m+1\text{ and }t<0,\\g(x',|t|),&\text{otherwise}.\end{cases}$$
--   For every smooth compactly supported test function $\varphi$ on the whole space,
--   $$\int_{\mathbb R^{m+1}}G_i\varphi=-\int_{\mathbb R^{m+1}}Ef\,\partial_i\varphi.$$
--   This identity expresses cancellation at the boundary: tangential derivatives reflect evenly and the normal derivative oddly. The $L^p$ assumptions supply integrability up to the boundary. A proof can cut tests off near $t=0$; in the normal direction use the odd test combination, whose vanishing at the boundary controls the derivative of the cutoff. The assertion includes $p=\infty$ and needs no finite-$p$ density theorem.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 2014-06-18, section 3.9, printed pp. 71–72, the reflection construction immediately before Theorem 3.41. https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . This is the auxiliary distributional identity needed for that construction, not a separately numbered source theorem.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Shared.integral_evenReflection_mul_testFunction (m : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (i : Fin (m + 1)) (f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : MemLp f p (volume.restrict (HunterPDE.Compactness.upperHalfSpace m)))
    (hg : MemLp g p (volume.restrict (HunterPDE.Compactness.upperHalfSpace m)))
    (hd : HunterPDE.Shared.HasWeakDeriv (HunterPDE.Compactness.upperHalfSpace m)
      (Pi.single i 1) f g)
    (φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hφ : HunterPDE.Shared.IsTestFunction Set.univ φ) :
    (∫ x : EuclideanSpace ℝ (Fin (m + 1)),
      (if i = Fin.last m ∧ x (Fin.last m) < 0 then
        -g (WithLp.toLp 2 (fun j => if j = Fin.last m then |x j| else x j))
       else g (WithLp.toLp 2 (fun j => if j = Fin.last m then |x j| else x j))) * φ x) =
    -(∫ x : EuclideanSpace ℝ (Fin (m + 1)),
      f (WithLp.toLp 2 (fun j => if j = Fin.last m then |x j| else x j)) *
        HunterPDE.Shared.multiDeriv φ (Pi.single i 1) x) := by sorry
