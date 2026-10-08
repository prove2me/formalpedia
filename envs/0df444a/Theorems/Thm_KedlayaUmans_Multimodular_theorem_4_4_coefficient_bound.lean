-- Prove2me | Theorems.Thm_KedlayaUmans_Multimodular_theorem_4_4_coefficient_bound
-- name    : KedlayaUmans.Multimodular.theorem_4_4_coefficient_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:15.648991+00:00
-- url     : https://prove2.me/theorems/e22960b0-4b47-4747-b515-3eea14c8332f
-- title:
--   Proof of Theorem 4.4 — $\tilde f(\tilde\alpha) \in \mathbb Z[Z]$ has degree $\le (e-1)dm$ and coefficients in $\{0,\dots,M-1\}$
-- statement:
--   Let $r \ge 1$, let $E(Z) \in (\mathbb Z/r\mathbb Z)[Z]$ be monic of degree $e \ge 1$, and let $R = (\mathbb Z/r\mathbb Z)[Z]/(E(Z))$. Let $m \ge 1$ and $d \ge 1$, let $f \in R[X_0,\dots,X_{m-1}]$ have degree at most $d-1$ in each variable, and let $\alpha \in R^m$. Let $\tilde f \in \mathbb Z[Z][X_0,\dots,X_{m-1}]$ and $\tilde\alpha \in \mathbb Z[Z]^m$ be the lifts (canonical representatives of degree at most $e-1$, with coefficients in $\{0,\dots,r-1\}$), and $M = d^m(e(r-1))^{(d-1)m+1}+1$. Then the polynomial $\tilde f(\tilde\alpha) \in \mathbb Z[Z]$ satisfies
--   $$\deg \tilde f(\tilde\alpha) \le (e-1)dm \quad\text{and}\quad 0 \le [Z^j]\,\tilde f(\tilde\alpha) \le M-1 \ \text{ for every } j \ge 0.$$
--
--   The bound puts $\tilde f(\tilde\alpha)$ in the class of polynomials that are determined by their value at $Z = M$ modulo $M^{(e-1)dm+1}$, which is what the extension-ring algorithm recovers.
--
--   **Formalization Note** The hypotheses $m \ge 1$ (needed for $(e-1)((d-1)m+1) \le (e-1)dm$), $d \ge 1$ and $e \ge 1$ are implicit in the paper.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 15, proof of Theorem 4.4

import Mathlib
import Definitions.Def_KedlayaUmans_Multimodular_Algorithm
import Definitions.Def_KedlayaUmans_Multimodular_ExtensionRing

namespace KedlayaUmans.Multimodular

open Polynomial

/-- **Proof of Theorem 4.4** (p. 15): `f̃(α̃) ∈ ℤ[Z]` has degree at most `(e-1)dm` and every
coefficient in `{0, …, M-1}`, `M = d^m (e(r-1))^{(d-1)m+1} + 1`. -/
theorem theorem_4_4_coefficient_bound {r m : ℕ} [NeZero r] (d : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (E : (ZMod r)[X]) (hE : E.Monic) (he : 1 ≤ E.natDegree)
    (f : MvPolynomial (Fin m) (AdjoinRoot E)) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (α : Fin m → AdjoinRoot E) :
    (MvPolynomial.eval (liftPointExt hE α) (liftPolyExt hE f)).natDegree ≤
        digitDegree d m E.natDegree ∧
      ∀ j : ℕ, 0 ≤ (MvPolynomial.eval (liftPointExt hE α) (liftPolyExt hE f)).coeff j ∧
        (MvPolynomial.eval (liftPointExt hE α) (liftPolyExt hE f)).coeff j ≤
          ((bigM d m E.natDegree r : ℕ) : ℤ) - 1 := by sorry

end KedlayaUmans.Multimodular
