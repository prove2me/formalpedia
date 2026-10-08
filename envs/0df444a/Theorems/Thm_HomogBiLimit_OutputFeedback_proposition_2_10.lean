-- Prove2me | Theorems.Thm_HomogBiLimit_OutputFeedback_proposition_2_10
-- name    : HomogBiLimit.OutputFeedback.proposition_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:16.781116+00:00
-- url     : https://prove2.me/theorems/ca9f0502-81b3-4c42-b7e3-62c8cfe3ba2c
-- title:
--   Proposition 2.10 (corrected) — composition of functions homogeneous in the 0-limit or the ∞-limit
-- statement:
--   Let $\phi:\mathbb R^n\to\mathbb R$ and $\zeta:\mathbb R\to\mathbb R$.
--
--   1. (**0-limit**) Suppose $\phi$ is homogeneous in the 0-limit with triple $(r_\phi,d_\phi,\phi_0)$, $d_\phi>0$, and $\zeta$ is homogeneous in the 0-limit with triple $(r_\zeta,d_\zeta,\zeta_0)$ (scalar weight $r_\zeta>0$, degree $d_\zeta\ge0$). If $\zeta_0\circ\phi_0$ is not identically zero, then $\zeta\circ\phi$ is homogeneous in the 0-limit with triple
--   $$\Bigl(r_\phi,\ \frac{d_\zeta\,d_\phi}{r_\zeta},\ \zeta_0\circ\phi_0\Bigr).$$
--   2. (**∞-limit**) The same holds with ∞ in place of 0, under the additional assumption $d_{\zeta,\infty}>0$.
--
--   This rule is how the paper certifies that its recursively built feedbacks and observer gains are homogeneous in the bi-limit.
--
--   **Formalization Note** The statement printed in the paper is false without two corrections, both added here. (a) It does not assume $\zeta_0\circ\phi_0\not\equiv0$, which the definition of homogeneity requires of an approximating function: $\phi(x)=|x|$ and $\zeta(s)=\max(-s,0)$ give $\zeta\circ\phi\equiv0$. (b) In the ∞-limit with $d_{\zeta,\infty}=0$ it fails: on $\mathbb R^2$ take $\phi(x)=x_1$ (weight $(1,1)$, degree 1) and $\zeta(s)=1-e^{-s^2}$ (weight 1, degree 0, $\zeta_\infty\equiv1$); then $\zeta(\phi(\lambda x))=0\ne1$ at $x=(0,1)$ for every $\lambda$. The paper uses the proposition only with $\zeta$ a signed power of positive degree, where both extra assumptions hold. $\zeta$ is viewed as a function on $\mathbb R^1$, $v\mapsto\zeta(v_1)$, with the constant weight $r_\zeta$.
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, p. 5, Proposition 2.10 (corrected: composite approximation not identically zero; positive degree of ζ in the ∞-limit)

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

namespace HomogBiLimit.OutputFeedback

/-- Proposition 2.10 (composition), p. 5, with two corrections (see the natural-language
statement): the composite approximating function `ζ₀ ∘ φ₀` (resp. `ζinf ∘ φinf`) is assumed
not identically zero, and in the ∞-limit the degree of `ζ` is assumed positive.
The scalar function `ζ : ℝ → ℝ` is viewed on `ℝ¹` as `v ↦ ζ(v₁)`, with scalar weight. -/
theorem proposition_2_10 {n : ℕ} (φ φ₀ φinf : (Fin n → ℝ) → ℝ) (ζ ζ₀ ζinf : ℝ → ℝ) :
    (∀ (rφ : Fin n → ℝ) (dφ rζ dζ : ℝ),
      0 < dφ → IsHomogZero φ rφ dφ φ₀ →
      IsHomogZero (fun v : Fin 1 → ℝ => ζ (v 0)) (fun _ => rζ) dζ (fun v => ζ₀ (v 0)) →
      (∃ x, ζ₀ (φ₀ x) ≠ 0) →
      IsHomogZero (fun x => ζ (φ x)) rφ (dζ * dφ / rζ) (fun x => ζ₀ (φ₀ x))) ∧
    (∀ (rφ : Fin n → ℝ) (dφ rζ dζ : ℝ),
      0 < dφ → 0 < dζ → IsHomogInfty φ rφ dφ φinf →
      IsHomogInfty (fun v : Fin 1 → ℝ => ζ (v 0)) (fun _ => rζ) dζ (fun v => ζinf (v 0)) →
      (∃ x, ζinf (φinf x) ≠ 0) →
      IsHomogInfty (fun x => ζ (φ x)) rφ (dζ * dφ / rζ) (fun x => ζinf (φinf x))) := by sorry

end HomogBiLimit.OutputFeedback
