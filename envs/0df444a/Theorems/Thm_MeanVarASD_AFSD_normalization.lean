-- Prove2me | Theorems.Thm_MeanVarASD_AFSD_normalization
-- name    : MeanVarASD.AFSD.normalization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:41.228341+00:00
-- url     : https://prove2.me/theorems/821566d4-19c9-4414-8fd3-04fb13535378
-- title:
--   Proofs of Theorems 7 and 3, pp. 5–6 — every v ∈ U_{γ,γ} is a·u + b with a ≥ 0, u(δ) = 0 and γ ≤ u′ ≤ 1
-- statement:
--   Let $0<\gamma\le1$ and let $v\in\mathcal U_{\gamma,\gamma}$, that is, $v$ is continuously differentiable and $0\le\gamma v'(y)\le v'(x)$, $0\le\gamma v'(x)\le v'(y)$ for all $x\le y$. Fix $\delta\in\mathbb R$. Then there are constants $a\ge0$ and $b$ and a differentiable function $u$ with
--   $$u(\delta)=0,\qquad \gamma\le u'(x)\le1\ \text{ for all }x,\qquad v=a\,u+b.$$
--
--   This is the normalization with which the proof of Theorem 7 begins ("any utility that belongs to the class $\mathcal U_{\gamma,\gamma}$ is an affine transformation of $u$"), carried out as in the beginning of the proof of Theorem 3 with $u=(v-v(\delta))/\sup v'$. It reduces the comparison $\mathbb E\,v(X)\le\mathbb E\,v(Y)$ to normalized utilities.
--
--   **Formalization Note** The constant $a$ may be $0$: it covers a constant $v$, where $\sup v'=0$ and the paper's quotient is $0/0$ (then any normalized $u$, e.g. $x\mapsto x-\delta$, works). The supremum of $v'$ does not appear in the statement.
-- source:
--   Müller, Scarsini, Tsetlin & Winkler, Ranking distributions when only means and variances are known, INSEAD Working Paper 2020/36/DSC (31 July 2020; SSRN 3440103), p. 6 (PDF 7), proof of Theorem 7, first paragraph; p. 5 (PDF 6), proof of Theorem 3, first display

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs

namespace MeanVarASD.AFSD

/-- Proof of Theorem 7, p. 6, and proof of Theorem 3, p. 5: for `0 < γ ≤ 1`, every
`v ∈ U_{γ,γ}` is a non-negative multiple of a function `u` with `u(δ) = 0` and
`γ ≤ u′ ≤ 1`, plus a constant. -/
theorem normalization (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (v : ℝ → ℝ) (hv : v ∈ UClass γ γ)
    (δ : ℝ) :
    ∃ a b : ℝ, 0 ≤ a ∧ ∃ u : ℝ → ℝ, Differentiable ℝ u ∧ u δ = 0 ∧
      (∀ x, γ ≤ deriv u x ∧ deriv u x ≤ 1) ∧ ∀ x, v x = a * u x + b := by sorry

end MeanVarASD.AFSD
