-- Prove2me | Theorems.Thm_KedlayaUmans_Reduction_correctness_congruence
-- name    : KedlayaUmans.Reduction.correctness_congruence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:46.69458+00:00
-- url     : https://prove2.me/theorems/74935c39-f9e7-4965-bccd-8672a655dc7a
-- title:
--   Proof of Theorem 3.1 — $f'(g_{0,0}, \dots, g_{m-1,\ell-1}) \equiv f(g_0, \dots, g_{m-1}) \pmod{h}$
-- statement:
--   Let $R$ be a commutative ring, $2 \le d_0 < d$, $\ell = \lceil \log_{d_0} d \rceil$, and let $f \in R[X_0, \dots, X_{m-1}]$ have individual degrees at most $d - 1$. Let $g_0, \dots, g_{m-1}, h \in R[X]$ with the leading coefficient of $h$ a unit. With $f' = \psi_{d_0,\ell}(f)$ and $g_{i,j} = g_i^{d_0^{\,j}} \bmod h$ (Steps 1 and 2 of the algorithm),
--   $$
--   f'\bigl(g_{0,0}(X), \dots, g_{m-1,\ell-1}(X)\bigr) \equiv f\bigl(g_0(X), \dots, g_{m-1}(X)\bigr) \pmod{h(X)} .
--   $$
--
--   This is the observation from which the paper derives the correctness of the reduction: the polynomial reconstructed in Step 5 has the right residue modulo $h$.
--
--   **Formalization Note** The congruence is stated as divisibility, $h \mid f'(g_{\cdot,\cdot}) - f(g)$, with both compositions as `MvPolynomial.aeval`. The hypotheses on the degrees of $g_i$ and $h$ from Theorem 3.1 are not needed for this congruence and are omitted, which makes the statement more general.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 10, proof of Theorem 3.1 (displayed congruence after Step 6)

import Mathlib
import Definitions.Def_KedlayaUmans_Reduction_Algorithm

namespace KedlayaUmans.Reduction

open Polynomial

theorem correctness_congruence {R : Type*} [CommRing R] {m d d₀ : ℕ}
    (hd₀ : 2 ≤ d₀) (hd₀d : d₀ < d)
    (f : MvPolynomial (Fin m) R) (hf : ∀ i, f.degreeOf i ≤ d - 1)
    (g : Fin m → R[X]) (h : R[X]) (hlc : IsUnit h.leadingCoeff) :
    h ∣ MvPolynomial.aeval (step2 d₀ d g h) (step1 d₀ d f) - MvPolynomial.aeval g f := by sorry

end KedlayaUmans.Reduction
