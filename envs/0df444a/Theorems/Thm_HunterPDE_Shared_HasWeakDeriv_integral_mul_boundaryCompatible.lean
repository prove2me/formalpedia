-- Prove2me | Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_integral_mul_boundaryCompatible
-- name    : HunterPDE.Shared.HasWeakDeriv.integral_mul_boundaryCompatible
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-15T18:21:56.916078+00:00
-- url     : https://prove2.me/theorems/d6f40424-8cf6-4816-b13c-14747edc8687
-- title:
--   Half-space weak integration by parts for boundary-compatible tests
-- statement:
--   Let $H=\{(x',t):t>0\}\subset\mathbb R^{m+1}$. Suppose $f,g$ are locally integrable for the restricted measure $\mathbf1_H\,dx$, including in neighborhoods of the boundary, and $g=\partial_i f$ weakly in the open half-space. Let $\psi\in C_c^\infty(\mathbb R^{m+1})$. If $i$ is the normal coordinate, assume $\psi(x',0)=0$; for tangential coordinates impose no boundary condition. Then
--   $$\int_H g\psi\,dx=-\int_H f\,\partial_i\psi\,dx.$$
--   Thus weak integration by parts extends from tests supported strictly inside $H$ to smooth ambient tests compatible with the direction of differentiation. A boundary cutoff has no tangential derivative. In the normal case, the zero boundary value gives $|\psi(x',t)|\le Ct$ on the relevant compact set, controlling the cutoff derivative term by an integrable multiple of $|f|$. This is an auxiliary distributional lemma derived from the reflection construction; it does not assume that an extension theorem has already been proved.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised June 18, 2014, section 3.9, printed pp. 71–72, reflection construction preceding Theorem 3.41, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf . This auxiliary lemma is derived for the distributional justification of the construction; it is not a separately numbered source theorem.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_HunterPDE_Compactness_HalfSpace

open MeasureTheory
set_option autoImplicit false

theorem HunterPDE.Shared.HasWeakDeriv.integral_mul_boundaryCompatible
    (m : ℕ) (i : Fin (m + 1)) (f g ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : LocallyIntegrable f (volume.restrict (HunterPDE.Compactness.upperHalfSpace m)))
    (hg : LocallyIntegrable g (volume.restrict (HunterPDE.Compactness.upperHalfSpace m)))
    (hd : HunterPDE.Shared.HasWeakDeriv (HunterPDE.Compactness.upperHalfSpace m)
      (Pi.single i 1) f g)
    (hψ : HunterPDE.Shared.IsTestFunction Set.univ ψ)
    (hb : i = Fin.last m → ∀ x, x (Fin.last m) = 0 → ψ x = 0) :
    (∫ x in HunterPDE.Compactness.upperHalfSpace m, g x * ψ x) =
      -(∫ x in HunterPDE.Compactness.upperHalfSpace m,
        f x * HunterPDE.Shared.multiDeriv ψ (Pi.single i 1) x) := by sorry
