-- Prove2me | Theorems.Thm_MarkushevichBasis_fourier_continuousMap_isMarkushevichBasis
-- name    : MarkushevichBasis.fourier_continuousMap_isMarkushevichBasis
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:51.39984+00:00
-- url     : https://prove2.me/theorems/0e947b90-0850-424c-aa16-c0610fad4b02
-- title:
--   The trigonometric system is a Markushevich basis of $C(\mathbb T)$
-- statement:
--   **The trigonometric system is a Markushevich basis of $C(\mathbb T)$.** Let $T>0$, let $\mathbb T=\mathbb R/T\mathbb Z$ carry its Haar probability measure $\mu$, let $C(\mathbb T)$ be the Banach space of continuous functions $\mathbb T\to\mathbb C$ with the uniform norm, and for $n\in\mathbb Z$ let $e_n(x)=e^{2\pi i n x/T}$ and
--   $$\widehat g(n)=\int_{\mathbb T}\overline{e_n(x)}\,g(x)\,d\mu(x)\qquad\bigl(g\in C(\mathbb T)\bigr).$$
--   Then every $g\mapsto\widehat g(n)$ is a continuous linear functional on $C(\mathbb T)$, and $\{(e_n,\widehat{\,\cdot\,}(n))\}_{n\in\mathbb Z}$ is a Markushevich basis of $C(\mathbb T)$:
--
--   1. $\widehat{e_m}(n)=\delta_{mn}$ for all $m,n\in\mathbb Z$;
--   2. the trigonometric polynomials are uniformly dense in $C(\mathbb T)$;
--   3. a continuous function all of whose Fourier coefficients vanish is identically $0$.
--
--   On pp. 157–158 the paper gives $C(\mathbb T)$ and $L^1(\mathbb T)$ as the normed completions of $C^\infty(\mathbb T)$ in which the exponential system, although its coefficient functionals stay continuous, is not a Schauder basis (on the platform: `SchauderBasis.not_exists_schauderBasis_continuousMap_fourier`), and on p. 438 it notes for $L^1(\mathbb T)$ that the system is nevertheless a Markushevich basis. This item is the corresponding statement for $C(\mathbb T)$.
--
--   **Deviation from the source.** The paper states the Markushevich property explicitly only for $L^1(\mathbb T)$ (p. 438); the $C(\mathbb T)$ case is the classical companion statement for the other example of pp. 157–158.
--
--   **Formalization Note.** $C(\mathbb T)$ is Mathlib's `C(AddCircle T, ℂ)` with the sup norm, $e_n$ is `fourier n` and $\widehat g(n)$ is `fourierCoeff g n` (integral against the Haar probability measure). The theorem asserts that the coefficient functionals exist as continuous linear functionals agreeing with `fourierCoeff`. The period $T>0$ is arbitrary (the paper takes $T=1$); the family is indexed by $\mathbb Z$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 438, §10.2 (second and third paragraphs; stated there for $L^1(\mathbb T)$), and pp. 157–158, §4.1.1 (the exponential system in $C(\mathbb T)$)

import Mathlib
import Definitions.Def_MarkushevichBasis_Basic

open MeasureTheory AddCircle

set_option autoImplicit false

namespace MarkushevichBasis

theorem fourier_continuousMap_isMarkushevichBasis (T : ℝ) [Fact (0 < T)] :
    ∃ c : ℤ → StrongDual ℂ C(AddCircle T, ℂ),
      (∀ (n : ℤ) (g : C(AddCircle T, ℂ)), c n g = fourierCoeff (⇑g) n) ∧
      IsMarkushevichBasis (fun n : ℤ => fourier (T := T) n) c := by sorry

end MarkushevichBasis
