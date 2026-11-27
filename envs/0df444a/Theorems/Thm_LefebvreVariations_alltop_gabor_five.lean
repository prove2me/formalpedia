-- Prove2me | Theorems.Thm_LefebvreVariations_alltop_gabor_five
-- name    : LefebvreVariations.alltop_gabor_five
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:22:07.636164+00:00
-- url     : https://prove2.me/theorems/f14da2e1-5341-5065-bcf5-5c73c564860b
-- title:
--   Lefebvre's variations, No. 262 — on a theme by Herman and Strohmer: the Alltop Gabor dictionary for N equal to 5 has coherence 1 over the square root of 5
-- statement:
--   Let $N=5$, $\omega=e^{2\pi i/5}$, and let $f\in\mathbb{C}^5$ be the Alltop sequence
--   $$
--   f_n \;=\; 5^{-1/2}\,e^{2\pi i n^{3}/5},\qquad n=0,\dots,4 .
--   $$
--   For $k,j\in\{0,\dots,4\}$ let $\varphi^{(k)}_j\in\mathbb{C}^5$ be the vector with entries $\varphi^{(k)}_j(p)=f_{(p+k)\bmod 5}\,\omega^{pj}$, and let $\Phi=(\varphi_0|\cdots|\varphi_{24})\in\mathbb{C}^{5\times25}$ be the Gabor dictionary of $f$ (columns $H_if$, $H_i=M^{i\bmod5}T^{\lfloor i/5\rfloor}$, with $T$ the cyclic shift and $M=\operatorname{diag}(\omega^p)$). Then
--   $$
--   \|f\|_2=1,\qquad
--   \bigl|\langle\varphi^{(k)}_j,\varphi^{(k)}_{j'}\rangle\bigr|=\delta_{jj'},\qquad
--   \bigl|\langle\varphi^{(k)}_j,\varphi^{(k')}_{j'}\rangle\bigr|=\tfrac1{\sqrt5}\ \ (k\neq k'),\qquad
--   \mu(\Phi)=\max_{i\ne i'}|\langle\varphi_i,\varphi_{i'}\rangle|=\tfrac1{\sqrt5}.
--   $$
--   So $\Phi$ is a union of five orthonormal bases of $\mathbb{C}^5$ that are mutually unbiased, and its coherence is the Welch bound $1/\sqrt5$.
--
--   This is the case $N=5$, the smallest prime allowed, of the statement that for every prime $N\ge5$ the Alltop Gabor dictionary has coherence $1/\sqrt N$, the property that makes the radar compressed-sensing guarantee $K<\tfrac12(\sqrt N+1)$ work. For $N=5$ it is a finite computation with fifth roots of unity and the cubes modulo $5$.
--
--   **Formalization Note** The statement uses the platform definitions `alltop`, `blockAtom`, `gaborDict`, `ip`, `norm2` and `coherence` of `Def_CompressedSensingRadar_Basic` at `N = 5`, and is the parent `CompressedSensingRadar.alltop_properties` with `N := 5`. The coherence is the supremum over ordered pairs of distinct columns of the modulus of the Hermitian inner product (linear in the second slot).
--
--   **Why this is a variation.** This varies the open platform problem CompressedSensingRadar.alltop_properties (the Alltop Gabor frame is a union of N mutually unbiased bases with coherence 1/sqrt N for every prime N >= 5). It is the case N = 5, the smallest admissible prime, stated with the parent's own definitions; it is a finite computation with fifth roots of unity and cubes modulo 5, and a model for the cases N = 7, 11.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Herman and Strohmer, High-resolution radar via compressed sensing, IEEE Trans. Signal Process. 57 (2009), Properties 1 and 2 (as quoted on the platform parent CompressedSensingRadar.alltop_properties); built on W. O. Alltop, Complex sequences with low periodic correlations, IEEE Trans. Inform. Theory 26 (1980); both cited from memory, page and property numbers not verified. For N = 5 the statement was verified exactly for all 300 pairs of atoms by arithmetic in Z[zeta_5] (50 orthogonal pairs within the five blocks, 250 pairs of modulus 1/sqrt(5)) and numerically for the blockAtom form.

import Mathlib
import Definitions.Def_CompressedSensingRadar_Basic

set_option autoImplicit false

open CompressedSensingRadar

namespace LefebvreVariations

/-- **The Alltop Gabor frame for `N = 5`.** For the smallest admissible prime `N = 5`, the Alltop sequence
`f_n = 5^{-1/2} e^{2πi n³/5}` has unit norm, each block `Φ^{(k)} = D_k W_5` of the Gabor dictionary of `f` is
orthonormal, atoms of two different blocks have inner product of modulus `1/√5`, and the coherence of the whole
`5 × 25` Gabor dictionary equals `1/√5` (the Welch bound for `N = 5`, which makes the dictionary a union of five
mutually unbiased bases). This is Properties 1 and 2 of Herman and Strohmer, *High-resolution radar via compressed
sensing*, IEEE Trans. Signal Process. 57 (2009), built on Alltop, *Complex sequences with low periodic
correlations*, IEEE Trans. Inform. Theory 26 (1980) (both cited from memory; page numbers not verified).

**Formalization Note.** Same `alltop`, `blockAtom`, `gaborDict`, `coherence` and `norm2` as
`CompressedSensingRadar.alltop_properties`, at `N = 5` (the parent assumes `N` prime and `5 ≤ N`). -/
theorem alltop_gabor_five :
    norm2 (alltop 5) = 1 ∧
    (∀ k j j' : Fin 5,
      ‖ip (blockAtom 5 (alltop 5) k j) (blockAtom 5 (alltop 5) k j')‖ = if j = j' then 1 else 0) ∧
    (∀ k k' : Fin 5, k ≠ k' → ∀ j j' : Fin 5,
      ‖ip (blockAtom 5 (alltop 5) k j) (blockAtom 5 (alltop 5) k' j')‖ = 1 / Real.sqrt 5) ∧
    coherence (gaborDict 5 (alltop 5)) = 1 / Real.sqrt 5 := by
  sorry

end LefebvreVariations
