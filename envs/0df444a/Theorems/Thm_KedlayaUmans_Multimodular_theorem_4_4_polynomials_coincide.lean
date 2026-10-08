-- Prove2me | Theorems.Thm_KedlayaUmans_Multimodular_theorem_4_4_polynomials_coincide
-- name    : KedlayaUmans.Multimodular.theorem_4_4_polynomials_coincide
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:48:20.435318+00:00
-- url     : https://prove2.me/theorems/f945e69a-cfda-46a8-839a-bc1e1c240a8e
-- title:
--   Proof of Theorem 4.4 — $Q_i = \tilde f(\tilde\alpha_i)$, whose reduction modulo $r$ and $E(Z)$ is $f(\alpha_i)$
-- statement:
--   Keep the setting of the extension-ring algorithm: $r \ge 1$, $E$ monic of degree $e \ge 1$, $R = (\mathbb Z/r\mathbb Z)[Z]/(E(Z))$, $m \ge 1$, $d \ge 1$, and $f \in R[X_0,\dots,X_{m-1}]$ of degree at most $d-1$ in each variable. Let $\alpha \in R^m$, let $M = d^m(e(r-1))^{(d-1)m+1}+1$, $D = (e-1)dm$ and $r' = M^{D+1}$. Let $\bar f$ and $\bar\alpha$ be the reductions of the lifts $\tilde f$, $\tilde\alpha$ modulo $r'$ and $Z - M$. Let $\beta = \bar f(\bar\alpha) \in \mathbb Z/r'\mathbb Z$ be the true value, and let $Q(Z) = \sum_{j=0}^{D} c_j Z^j$ with $c_j = \lfloor n/M^j \rfloor \bmod M$ be the polynomial of base-$M$ digits of the representative $n \in \{0,\dots,r'-1\}$ of $\beta$. Then
--   $$Q = \tilde f(\tilde\alpha) \ \text{ in } \mathbb Z[Z], \qquad \text{and} \qquad \tilde f(\tilde\alpha) \bmod (r, E(Z)) = f(\alpha) \ \text{ in } R.$$
--
--   Together with Theorem 4.2, which says that Step 3 of the algorithm produces exactly $\beta$, this gives the correctness of the extension-ring algorithm.
--
--   **Formalization Note** The statement uses the true value $\bar f(\bar\alpha)$ in place of the output of Algorithm MULTIMODULAR, so that it is independent of Theorem 4.2. The polynomial $Q$ is the specific digit polynomial of Step 4, not an arbitrary polynomial with the two properties. "Reduction modulo $r$ and $E(Z)$" is coefficientwise reduction $\mathbb Z[Z] \to (\mathbb Z/r\mathbb Z)[Z]$ followed by the quotient map to $R$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 15, proof of Theorem 4.4

import Mathlib
import Definitions.Def_KedlayaUmans_Multimodular_Algorithm
import Definitions.Def_KedlayaUmans_Multimodular_ExtensionRing

namespace KedlayaUmans.Multimodular

open Polynomial

/-- **Proof of Theorem 4.4** (p. 15): the digit polynomial `Q` built from `β = f̄(ᾱ) ∈ ℤ/r′ℤ`
coincides with `f̃(α̃)`, and the reduction of `f̃(α̃)` modulo `r` and `E(Z)` is `f(α)`. -/
theorem theorem_4_4_polynomials_coincide {r m : ℕ} [NeZero r] (d : ℕ) (hd : 1 ≤ d)
    (hm : 1 ≤ m) (E : (ZMod r)[X]) (hE : E.Monic) (he : 1 ≤ E.natDegree)
    (f : MvPolynomial (Fin m) (AdjoinRoot E)) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (α : Fin m → AdjoinRoot E) :
    digitPoly (bigM d m E.natDegree r) (digitDegree d m E.natDegree)
        (MvPolynomial.eval
          (fun i => evalAtM (bigM d m E.natDegree r) (rPrime d m E.natDegree r)
            (liftPointExt hE α i))
          (MvPolynomial.map (evalAtM (bigM d m E.natDegree r) (rPrime d m E.natDegree r))
            (liftPolyExt hE f))).val =
        MvPolynomial.eval (liftPointExt hE α) (liftPolyExt hE f) ∧
      AdjoinRoot.mk E ((MvPolynomial.eval (liftPointExt hE α) (liftPolyExt hE f)).map
        (Int.castRingHom (ZMod r))) = MvPolynomial.eval α f := by sorry

end KedlayaUmans.Multimodular
