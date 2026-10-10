-- Prove2me | Theorems.Thm_NonconvexDRS_ADMM_theorem_5_5
-- name    : NonconvexDRS.ADMM.theorem_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:57.675704+00:00
-- url     : https://prove2.me/theorems/216106eb-065d-42cc-8e94-8fc9b7a12657
-- title:
--   Theorem 5.5, pp. 18–19 — one relaxed ADMM step on (1.2) is one DRS step on (Af) + (Bg)(b − ·) with γ = 1/β, with (i)–(v)
-- statement:
--   Let $f:\mathbb R^m\to\overline{\mathbb R}$ and $g:\mathbb R^n\to\overline{\mathbb R}$ be proper, $A\in\mathbb R^{p\times m}$, $B\in\mathbb R^{p\times n}$, $b\in\mathbb R^p$, and let $\beta>0$ be large enough that every ADMM minimization subproblem has a solution. Let $\lambda>0$, and let $(x^+,y^+,z^+)$ be obtained from $(x,y,z)\in\mathbb R^m\times\mathbb R^p\times\mathbb R^n$ by one ADMM update with relaxation $\lambda$. Set, as in (5.2),
--   $$s=Ax-\tfrac1\beta y,\quad u=Ax,\quad v=b-Bz,\qquad s^+=Ax^+-\tfrac1\beta y^+,\quad u^+=Ax^+,\quad v^+=b-Bz^+,$$
--   and $\varphi_1=(Af)$, $\varphi_2=(Bg)(b-\cdot)$, $\gamma=1/\beta$. Then
--   $$s^+=s+\lambda(v-u),\qquad u^+\in\operatorname{prox}_{\gamma\varphi_1}(s^+),\qquad v^+\in\operatorname{prox}_{\gamma\varphi_2}(2u^+-s^+),$$
--   that is, $(s^+,u^+,v^+)$ is one DRS step on $\varphi_1+\varphi_2$ from $s$. Moreover:
--   1. $\varphi_1(u^+)=(Af)(Ax^+)=f(x^+)$;
--   2. $\varphi_2(v^+)=(Bg)(Bz^+)=g(z^+)$;
--   3. $-y^+\in\hat\partial\varphi_1(u^+)=\hat\partial(Af)(Ax^+)$;
--   4. $-A^\top y^+\in\hat\partial f(x^+)$;
--   5. $\operatorname{dist}\big(-B^\top y^+,\hat\partial g(z^+)\big)\le\beta\|B\|\|Ax^++Bz^+-b\|$.
--
--   The theorem is the primal equivalence of the two algorithms for every relaxation parameter and without convexity: every property of nonconvex DRS transfers to ADMM through $\varphi_1$ and $\varphi_2$.
--
--   **Formalization Note** Properness of $f$ and $g$ is not printed in the theorem and is added: for $f\equiv+\infty$ the image function is $\equiv+\infty$ and (iii) fails. "Large enough penalty" is `SubproblemsSolvable`: both ADMM subproblems have a minimizer for all data, which is equivalent to $X_\beta(s)\neq\emptyset$ and the analogous condition for $g$ for every $s$. The ADMM subproblems omit the constant term ($g(z)$, resp. $f(x^+)$) of $\mathcal L_\beta$, which in $\overline{\mathbb R}$ could be $+\infty$ and make every point a minimizer. Claim 5 is stated in the stronger form that some $w\in\hat\partial g(z^+)$ satisfies $\|-B^\top y^+-w\|\le\beta\|B\|\|Ax^++Bz^+-b\|$; this is what the optimality condition of $z^+$ provides, and it avoids the distance to a possibly empty set. $\|B\|$ is the operator (spectral) norm and $\hat\partial$ the regular subdifferential `IsRegularSubgrad`.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, pp. 18–19, Theorem 5.5 (the three relations and (i)–(v)), with (5.2)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.ADMM

/-- Theorem 5.5 (Primal equivalence of DRS and ADMM), p. 18: one ADMM update with relaxation `λ`
and penalty `β`, read through `s := Ax - y/β`, `u := Ax`, `v := b - Bz` (5.2), is one DRS step on
`φ₁ := (Af)`, `φ₂ := (Bg)(b - ·)` with stepsize `γ := 1/β`; moreover (i)–(v) hold. -/
theorem theorem_5_5 {m n p : ℕ} (f : EuclideanSpace ℝ (Fin m) → EReal)
    (g : EuclideanSpace ℝ (Fin n) → EReal) (hf : NonconvexDRS.Tight.IsProper f) (hg : NonconvexDRS.Tight.IsProper g)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (b : EuclideanSpace ℝ (Fin p))
    (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (hsolv : SubproblemsSolvable f g A B b β)
    (x xp : EuclideanSpace ℝ (Fin m)) (y yp : EuclideanSpace ℝ (Fin p))
    (z zp : EuclideanSpace ℝ (Fin n))
    (hstep : IsADMMStep f g A B b β lam x y z xp yp zp) :
    let s := A x - (1 / β) • y
    let u := A x
    let v := b - B z
    let sp := A xp - (1 / β) • yp
    let up := A xp
    let vp := b - B zp
    (sp = s + lam • (v - u) ∧
      up ∈ NonconvexDRS.Tight.proxSet (imageFn A f) (1 / β) sp ∧
      vp ∈ NonconvexDRS.Tight.proxSet (fun t => imageFn B g (b - t)) (1 / β) ((2 : ℝ) • up - sp)) ∧
    imageFn A f up = f xp ∧
    imageFn B g (b - vp) = g zp ∧
    IsRegularSubgrad (imageFn A f) up (-yp) ∧
    IsRegularSubgrad f xp (-(ContinuousLinearMap.adjoint A yp)) ∧
    ∃ w, IsRegularSubgrad g zp w ∧
      ‖-(ContinuousLinearMap.adjoint B yp) - w‖ ≤ β * ‖B‖ * ‖A xp + B zp - b‖ := by sorry

end NonconvexDRS.ADMM
