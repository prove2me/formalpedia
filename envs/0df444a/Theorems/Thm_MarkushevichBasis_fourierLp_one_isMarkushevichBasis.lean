-- Prove2me | Theorems.Thm_MarkushevichBasis_fourierLp_one_isMarkushevichBasis
-- name    : MarkushevichBasis.fourierLp_one_isMarkushevichBasis
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:40.698831+00:00
-- url     : https://prove2.me/theorems/8b421af0-85a4-48a6-b015-73f3f56419f3
-- title:
--   The trigonometric system is a Markushevich basis of $L^1(\mathbb T)$
-- statement:
--   **The trigonometric system is a Markushevich basis of $L^1(\mathbb T)$.** Let $T>0$, let $\mathbb T=\mathbb R/T\mathbb Z$ carry its Haar probability measure $\mu$, and for $n\in\mathbb Z$ let $e_n(x)=e^{2\pi i n x/T}$ and
--   $$\widehat g(n)=\int_{\mathbb T}\overline{e_n(x)}\,g(x)\,d\mu(x)\qquad\bigl(g\in L^1(\mathbb T,\mu)\bigr)$$
--   be the $n$-th Fourier coefficient. Then every $g\mapsto\widehat g(n)$ is a continuous linear functional on $L^1(\mathbb T)$, and $\{(e_n,\widehat{\,\cdot\,}(n))\}_{n\in\mathbb Z}$ is a Markushevich basis of $L^1(\mathbb T)$:
--
--   1. $\widehat{e_m}(n)=\delta_{mn}$ for all $m,n\in\mathbb Z$;
--   2. the trigonometric polynomials are dense in $L^1(\mathbb T)$;
--   3. (uniqueness theorem) if $g\in L^1(\mathbb T)$ and $\widehat g(n)=0$ for every $n\in\mathbb Z$, then $g=0$ almost everywhere.
--
--   On p. 438 the paper contrasts this with the fact that the exponential system is an absolute Schauder basis of $C^\infty(\mathbb T)$ but not a Schauder basis of $L^1(\mathbb T)$ (on the platform: `SchauderBasis.not_exists_schauderBasis_L1_fourier`): coarsening the topology from $C^\infty(\mathbb T)$ to $L^1(\mathbb T)$ destroys the convergence of the basis projections but keeps the Markushevich property. This is the model case for the spectral Markushevich bases of Chapter 10.
--
--   **Formalization Note.** $L^1(\mathbb T)$ is Mathlib's `Lp ℂ 1 haarAddCircle`, $e_n$ is `fourierLp 1 n` and $\widehat g(n)$ is `fourierCoeff g n` (integral against the Haar probability measure). The theorem asserts that the coefficient functionals exist as continuous linear functionals agreeing with `fourierCoeff`, and that together with the $e_n$ they form a Markushevich basis. The period $T>0$ is arbitrary (the paper takes $T=1$). Being a Markushevich basis does not depend on an enumeration of $\mathbb Z$, so the family is indexed by $\mathbb Z$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 438, §10.2 (second and third paragraphs)

import Mathlib
import Definitions.Def_MarkushevichBasis_Basic

open MeasureTheory AddCircle

set_option autoImplicit false

namespace MarkushevichBasis

theorem fourierLp_one_isMarkushevichBasis (T : ℝ) [Fact (0 < T)] :
    ∃ c : ℤ → StrongDual ℂ (Lp ℂ 1 (haarAddCircle (T := T))),
      (∀ (n : ℤ) (g : Lp ℂ 1 (haarAddCircle (T := T))), c n g = fourierCoeff (⇑g) n) ∧
      IsMarkushevichBasis (fun n : ℤ => fourierLp (T := T) 1 n) c := by sorry

end MarkushevichBasis
