-- Prove2me | Theorems.Thm_IntLInfty_Kan_simplicial_pullback_forms
-- name    : IntLInfty.Kan.simplicial_pullback_forms
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:13:17.134405+00:00
-- url     : https://prove2.me/theorems/b43a7bb9-4c41-4ae6-9a62-29638af7e9cf
-- title:
--   Pullback of forms along simplicial affine maps
-- statement:
--   For $\theta:\{0,\dots,m\}\to\{0,\dots,m'\}$ let $A_\theta:\mathbb R^m\to\mathbb R^{m'}$ be the affine map sending the vertex $v_l$ of $\Delta^m$ to $v_{\theta(l)}$, and let $P_\theta\,\omega=A_\theta^*\omega$ be the pullback of forms (any $P$ given by this pointwise formula). Then $A_\theta(\Delta^m)\subseteq\Delta^{m'}$; the coface pullback is $(d^i)^*=P_{\delta^i}$; $$P_{\theta'}P_\theta=P_{\theta\circ\theta'},\qquad P_{\mathrm{id}}=\mathrm{id}\ \text{on}\ \Delta^m;$$ $P_\theta$ is linear, preserves degree, the class $C^r$ (with $d\omega$ of class $C^r$, $r\ge1$) and closedness, commutes with $d$ on $\Delta^m$, only depends on $\omega|_{\Delta^{m'}}$, and preserves pointwise convergence of coefficients on the simplex. Finally, convergence of $r$-jets of $C^r$ forms implies pointwise convergence of their coefficients on the simplex.
--
--   Role: the simplicial pullback calculus (cofaces, degeneracies and horn retractions) and the coefficient-convergence facts used by the closed-graph continuity arguments.
-- source:
--   Henriques, Integrating L-infinity algebras, Compositio Math. 144 (2008), arXiv:math/0603563v2, https://arxiv.org/abs/math/0603563, Convention 5.1 and proof of Lemma 5.9, pp. 14-15 (pullbacks along the simplicial affine maps)

import Mathlib
import Definitions.Def_IntLInfty_Kan_Forms

set_option autoImplicit false

namespace IntLInfty.Kan

theorem simplicial_pullback_forms (r : ℕ) (hr : 1 ≤ r)
    (P : (m m' : ℕ) → (Fin (m + 1) → Fin (m' + 1)) → Ω m' → Ω m)
    (hP : ∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m') (x : Fin m → ℝ),
      P m m' θ ω x = ExteriorAlgebra.map
        (Matrix.of fun (a : Fin m') (k : Fin m) =>
          (vertex m' (θ k.succ) - vertex m' (θ 0)) a).mulVecLin.dualMap
        (ω (vertex m' (θ 0) + (Matrix.of fun (a : Fin m') (k : Fin m) =>
          (vertex m' (θ k.succ) - vertex m' (θ 0)) a).mulVecLin x))) :
    (∀ (m : ℕ) (i : Fin (m + 2)) (ω : Ω (m + 1)), pull m i ω = P m (m + 1) i.succAbove ω) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)), ∀ x ∈ simplex m,
      vertex m' (θ 0) + (Matrix.of fun (a : Fin m') (k : Fin m) =>
        (vertex m' (θ k.succ) - vertex m' (θ 0)) a).mulVecLin x ∈ simplex m') ∧
    (∀ (m m' m'' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (θ' : Fin (m'' + 1) → Fin (m + 1))
      (ω : Ω m'), P m'' m θ' (P m m' θ ω) = P m'' m' (θ ∘ θ') ω) ∧
    (∀ (m : ℕ) (ω : Ω m), ∀ x ∈ simplex m, P m m id ω x = ω x) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m'),
      P m m' θ (ω + ω') = P m m' θ ω + P m m' θ ω') ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m'),
      P m m' θ (ω - ω') = P m m' θ ω - P m m' θ ω') ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (c : ℝ) (ω : Ω m'),
      P m m' θ (c • ω) = c • P m m' θ ω) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (n : ℕ) (ω : Ω m'),
      IsDeg n ω → IsDeg n (P m m' θ ω)) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m'), IsCr r ω → IsCr r (P m m' θ ω)) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m'),
      IsCr r ω → IsClosedForm ω → IsClosedForm (P m m' θ ω)) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω : Ω m'),
      (∀ I, ContDiffOn ℝ r (coeff ω I) (simplex m')) →
        ∀ x ∈ simplex m, extD (P m m' θ ω) x = P m m' θ (extD ω) x) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ω ω' : Ω m'),
      (∀ x ∈ simplex m', ω x = ω' x) → ∀ x ∈ simplex m, P m m' θ ω x = P m m' θ ω' x) ∧
    (∀ (m m' : ℕ) (θ : Fin (m + 1) → Fin (m' + 1)) (ωk : ℕ → Ω m') (ω : Ω m'),
      (∀ I, ∀ x ∈ simplex m',
        Filter.Tendsto (fun k => coeff (ωk k) I x) Filter.atTop (nhds (coeff ω I x))) →
      ∀ J, ∀ x ∈ simplex m, Filter.Tendsto (fun k => coeff (P m m' θ (ωk k)) J x) Filter.atTop
        (nhds (coeff (P m m' θ ω) J x))) ∧
    (∀ (r' m : ℕ) (ωk : ℕ → Ω m) (ω : Ω m), (∀ k, IsCr r' (ωk k)) → IsCr r' ω →
      Filter.Tendsto (fun k => jet r' (ωk k)) Filter.atTop (nhds (jet r' ω)) →
      ∀ I, ∀ x ∈ simplex m,
        Filter.Tendsto (fun k => coeff (ωk k) I x) Filter.atTop (nhds (coeff ω I x))) := by sorry

end IntLInfty.Kan
