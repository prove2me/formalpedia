-- Prove2me | Theorems.Thm_GeomDRSub_lemma_4_1
-- name    : GeomDRSub.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:03.71024+00:00
-- url     : https://prove2.me/theorems/fb6c88b3-6728-47d9-8386-fd0b994e0583
-- title:
--   Lemma 4.1 — comparison with every fractional comparator
-- statement:
--   Let $\zeta\in[0,1]$ and let $f:[0,1]^d\to\mathbb R$ be nonnegative, continuously differentiable and DR-submodular. For all $x,o\in[0,1]^d$,
--   $$
--   f(o)+c_\zeta f(\mathbf 0)-\frac1{\alpha(\zeta)}\,f\big(h_\zeta(x)\big)\le\big\langle g_\zeta(f,x),\,o-x\big\rangle ,
--   $$
--   where $c_\zeta=\max\{1/2,1-\zeta\}$, $\alpha(\zeta)=4c_\zeta/(2c_\zeta+1)^2$, $h_\zeta$ is the action map and $g_\zeta(f,x)$ the field. In addition, for each fixed $f$, the field $x\mapsto g_\zeta(f,x)$ is Borel measurable on $[0,1]^d$.
--
--   The comparator $o$ is an arbitrary point of the cube, not only of a feasible set. The measurability makes $g_\zeta(f,x_t)$ a random vector when the state $x_t$ is random.
--
--   Differences from the source:
--   - encoding: f : [0,1]^d → ℝ continuously differentiable, gradient continuously extended to the boundary → f : ℝ^d → ℝ with ContDiffOn ℝ 1 f (cube d), gradient = within-cube derivative gradQ; reason: only the values on the cube matter; for d ≥ 1 the within-cube derivative is the continuous extension of the interior gradient
--   - encoding: the permutation π sorting µ with ties by increasing index → the strict order Before ζ x; reason: the order and the permutation determine each other
--   - encoding: x ↦ g_ζ(f,x) Borel measurable on [0,1]^d → Measurable on the subtype cube d (subspace σ-algebra of the Borel σ-algebra); reason: same statement; the domain of the field is the cube
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Lemma 4.1, p.11, Eq. (16)

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_GeomDRSub_cZeta
import Definitions.Def_GeomDRSub_alphaLow
import Definitions.Def_GeomDRSub_hAct
import Definitions.Def_GeomDRSub_field

namespace GeomDRSub

/-- **Lemma 4.1 (comparison with every fractional comparator).** Aggarwal–Lu, arXiv:2610.00545,
p.11: "For every `ζ ∈ [0, 1]`, every nonnegative continuously differentiable DR-submodular function
`f : [0, 1]^d → ℝ`, and all `x, o ∈ [0, 1]^d`, we have
`f(o) + c_ζ f(0) − (1/α(ζ)) f(h_ζ(x)) ≤ ⟨g_ζ(f, x), o − x⟩`, (16)
where `h_ζ(x)` and `α(ζ)` are defined in (11) and `g_ζ(f, x)` in (15). In addition, for each fixed
`f`, the field `x ↦ g_ζ(f, x)` is Borel measurable."

Both clauses are stated.

**Formalization Note.** The field is measurable as a map on the cube (the subtype `cube d` with
the subspace σ-algebra of the Borel σ-algebra of `ℝᵈ`), which is the page's domain `[0,1]^d`. -/
theorem lemma_4_1 {d : ℕ} (ζ : ℝ) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf0 : ∀ y ∈ cube d, 0 ≤ f y) (hf : IsDRSubmodular f) :
    (∀ x ∈ cube d, ∀ o ∈ cube d,
        f o + cZeta ζ * f 0 - (1 / alphaLow ζ) * f (hAct ζ x) ≤ inner ℝ (field ζ f x) (o - x)) ∧
      Measurable (fun x : cube d => field ζ f (x : EuclideanSpace ℝ (Fin d))) := by sorry

end GeomDRSub
