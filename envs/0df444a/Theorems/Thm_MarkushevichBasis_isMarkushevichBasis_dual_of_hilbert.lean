-- Prove2me | Theorems.Thm_MarkushevichBasis_isMarkushevichBasis_dual_of_hilbert
-- name    : MarkushevichBasis.isMarkushevichBasis_dual_of_hilbert
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:37.029805+00:00
-- url     : https://prove2.me/theorems/2ea5ffcf-3537-4eb1-88e8-3988f2e36e60
-- title:
--   The functionals of a Markushevich basis of a Hilbert space form a Markushevich basis of the dual space
-- statement:
--   **Dual Markushevich basis in a Hilbert space.** Let $H$ be a Hilbert space over $\mathbb K\in\{\mathbb R,\mathbb C\}$ with dual Banach space $H'$, let $J\colon H\to H''$, $J(x)(\varphi)=\varphi(x)$, be the canonical embedding, and let $\{(x_i,f_i)\}_{i\in\iota}$ be a Markushevich basis of $H$: $f_i(x_j)=\delta_{ij}$, the span of the $x_i$ is dense in $H$, and the $f_i$ separate the points of $H$. Then $\{(f_i,J x_i)\}_{i\in\iota}$ is a Markushevich basis of $H'$ (with its norm topology, which is the strong topology). In particular
--   $$\overline{\operatorname{span}}^{\,\|\cdot\|}\{f_i : i\in\iota\}=H',$$
--   i.e. the linear span of the coefficient functionals is dense in $H'$ for the norm (strong) topology, and not merely for the weak-$*$ topology $\sigma(H',H)$ (which is what totality says).
--
--   This is Remark 10.2.1.2 of the paper (p. 440), which deduces it from reflexivity and the cited result of Jarchow; it is what allows the paper to make no distinction between weak and strong density of the linear spans of the basis elements in the Hilbert spaces of Chapter 10 (pp. 440–441).
--
--   **Formalization Note.** The dual is Mathlib's `StrongDual 𝕜 H` with its operator-norm topology and the canonical embedding is `NormedSpace.inclusionInDoubleDual 𝕜 H`. The scalar field may be any `RCLike` field (the paper works over $\mathbb C$) and the index type is arbitrary (the paper uses sequences); the statement holds verbatim in this generality.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 440, Remark 10.2.1.2; classical reference: H. Jarchow, Locally Convex Spaces, B. G. Teubner, Stuttgart, 1981, Part II, Ch. 8, §8.2, Prop. 1, p. 149 (as cited by the paper there)

import Mathlib
import Definitions.Def_MarkushevichBasis_Basic

set_option autoImplicit false

namespace MarkushevichBasis

theorem isMarkushevichBasis_dual_of_hilbert {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {ι : Type*} (x : ι → H) (f : ι → StrongDual 𝕜 H) (hxf : IsMarkushevichBasis x f) :
    IsMarkushevichBasis f (fun i => NormedSpace.inclusionInDoubleDual 𝕜 H (x i)) := by sorry

end MarkushevichBasis
