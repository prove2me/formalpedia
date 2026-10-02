-- Prove2me | Theorems.Thm_LeblSCV_CR_real_analytic_hypersurface_normal_form
-- name    : LeblSCV.CR.real_analytic_hypersurface_normal_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T08:05:16.035661+00:00
-- url     : https://prove2.me/theorems/a4773c85-491c-4f85-b39d-353f8800f1a3
-- title:
--   Proposition 3.2.8 — a real-analytic hypersurface is $\bar w = \Phi(z, \bar z, w)$
-- statement:
--   Let $M \subset \mathbb{C}^n$ be a real-analytic hypersurface and $p \in M$. Then after a translation and a rotation by a unitary matrix, $p = 0$, and near the origin, in coordinates $(z, w) \in \mathbb{C}^{n-1} \times \mathbb{C}$, the hypersurface $M$ is given by
--   $$\bar w = \Phi(z, \bar z, w),$$
--   where $\Phi(z, \zeta, w)$ is holomorphic on a neighborhood of the origin in $\mathbb{C}^{n-1} \times \mathbb{C}^{n-1} \times \mathbb{C}$, the function $\Phi$ and its derivatives $\partial \Phi/\partial z_k$, $\partial\Phi/\partial\zeta_k$ vanish at the origin for all $k$, and
--   $$w = \bar\Phi\big(\zeta, z, \Phi(z, \zeta, w)\big) \quad \text{for all } z, \zeta, w \text{ near the origin},$$
--   where $\bar\Phi(a, b, c) = \overline{\Phi(\bar a, \bar b, \bar c)}$ is the function with conjugated power series coefficients.
--
--   **Formalization Note.** Stated for $n = m + 1$ (a hypersurface in $\mathbb{C}^0$ is empty, so nothing is lost); $z$ is the first $m$ coordinates and $w$ the last. The change of coordinates is $q \mapsto U(q - p)$ with $U$ in `Matrix.unitaryGroup`. "Near the origin" is explicit: an open $W \ni 0$ in $\mathbb{C}^n$ on which the transformed $M$ equals $\{\bar w = \Phi(z, \bar z, w)\}$, an open $N \ni 0$ on which $\Phi$ is holomorphic (`DifferentiableOn ℂ`) and which contains $(z, \bar z, w)$ for $(z,w) \in W$, and an open $N' \subset N$, $0 \in N'$, on which the identity holds (with the point $(\bar\zeta, \bar z, \overline{\Phi(z,\zeta,w)})$ in $N$). The vanishing of $\partial\Phi/\partial z_k$ and $\partial\Phi/\partial\zeta_k$ is `fderiv ℂ Φ 0 (v, u, 0) = 0` for all $v, u$. Only the displayed statement is formalized; the page's further remarks (a basis of $T^{(0,1)}M$ and the uniqueness of the complexification $\mathcal{M}$) are not.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 112, Proposition 3.2.8

import Mathlib
import Definitions.Def_LeblSCV_CR_IsRealAnalyticHypersurface

open ComplexConjugate

namespace LeblSCV.CR

/-- Proposition 3.2.8 (Lebl, p. 112), for `ℂⁿ` with `n = m + 1`, coordinates
`(z, w) ∈ ℂᵐ × ℂ` (`z` = the first `m` coordinates, `w` = the last): if `M ⊂ ℂⁿ` is a
real-analytic hypersurface and `p ∈ M`, then after the translation and unitary rotation
`q ↦ U (q − p)` (which sends `p` to `0`), near the origin `M` is given by `w̄ = Φ(z, z̄, w)`,
where `Φ(z, ζ, w)` is holomorphic on a neighbourhood `N` of the origin of `ℂᵐ × ℂᵐ × ℂ`,
`Φ`, `∂Φ/∂z_k`, `∂Φ/∂ζ_k` vanish at the origin, and `w = Φ̄(ζ, z, Φ(z, ζ, w))` for all
`(z, ζ, w)` near the origin, where `Φ̄(a, b, c) = conj (Φ(ā, b̄, c̄))`. -/
theorem real_analytic_hypersurface_normal_form {m : ℕ} (M : Set (Fin (m + 1) → ℂ))
    (hM : IsRealAnalyticHypersurface M) (p : Fin (m + 1) → ℂ) (hp : p ∈ M) :
    ∃ U ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ,
    ∃ (W : Set (Fin (m + 1) → ℂ)) (N N' : Set ((Fin m → ℂ) × (Fin m → ℂ) × ℂ))
      (Φ : (Fin m → ℂ) × (Fin m → ℂ) × ℂ → ℂ),
      IsOpen W ∧ (0 : Fin (m + 1) → ℂ) ∈ W ∧
      IsOpen N ∧ (0 : (Fin m → ℂ) × (Fin m → ℂ) × ℂ) ∈ N ∧ DifferentiableOn ℂ Φ N ∧
      Φ 0 = 0 ∧ (∀ v u : Fin m → ℂ, fderiv ℂ Φ 0 (v, u, 0) = 0) ∧
      (∀ x ∈ W, ((fun k : Fin m => x k.castSucc), (fun k : Fin m => conj (x k.castSucc)),
        x (Fin.last m)) ∈ N) ∧
      (fun q => Matrix.mulVec U (q - p)) '' M ∩ W =
        {x | x ∈ W ∧ conj (x (Fin.last m)) =
          Φ ((fun k : Fin m => x k.castSucc), (fun k : Fin m => conj (x k.castSucc)),
            x (Fin.last m))} ∧
      IsOpen N' ∧ (0 : (Fin m → ℂ) × (Fin m → ℂ) × ℂ) ∈ N' ∧ N' ⊆ N ∧
      ∀ t ∈ N',
        ((fun k => conj (t.2.1 k)), (fun k => conj (t.1 k)), conj (Φ t)) ∈ N ∧
        t.2.2 = conj (Φ ((fun k => conj (t.2.1 k)), (fun k => conj (t.1 k)),
          conj (Φ t))) := by sorry

end LeblSCV.CR
