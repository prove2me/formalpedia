-- Prove2me | Theorems.Thm_MasulloGRH_schwartzBruhat_modulus_multiplier
-- name    : MasulloGRH.schwartzBruhat_modulus_multiplier
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T19:47:51.467273+00:00
-- url     : https://prove2.me/theorems/4b285e4e-6dae-455a-9e7f-883951ca8765
-- title:
--   Multiplying by (|x|^{b₁}+|x|^{b₂})⁻¹ is continuous on S(H)
-- statement:
--   Let $H$ be a second-countable, locally compact, Hausdorff abelian group, and let $\mu\colon H\to\mathbb R_{>0}$ be a continuous homomorphism. Let $b_1\le 0\le b_2$. Then the multiplier $f\mapsto (\mu^{b_1}+\mu^{b_2})^{-1}f$ maps the Schwartz–Bruhat space $\mathcal S(H)$ to itself and is continuous. On a stage $(\Gamma,k_1,\pi)$, $\mu|_\Gamma=\chi\circ\pi$ with $\chi(x,z,a,b)=e^{\langle\lambda,x\rangle+\langle\nu,a\rangle}$, so the multiplier is $u(s)=1/(e^{b_1s}+e^{b_2s})$ evaluated at $s=\langle\lambda,x\rangle+\langle\nu,a\rangle$, and $u$ has all derivatives bounded. This is the multiplier used in the interpolation Lemma D.3.3.2.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.3.3.2

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

universe u

namespace MasulloGRH

theorem schwartzBruhat_modulus_multiplier
    (H : Type u) [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H] [SecondCountableTopology H] (μ : H → ℝ) (hμc : Continuous μ)
    (hμp : ∀ x, 0 < μ x) (hμm : ∀ x y, μ (x * y) = μ x * μ y) (b₁ b₂ : ℝ)
    (hb₁ : b₁ ≤ 0) (hb₂ : 0 ≤ b₂) :
    ∃ M : SchwartzBruhat H →L[ℂ] SchwartzBruhat H, ∀ (f : SchwartzBruhat H) (x : H),
      (M f).toFun x = ((μ x ^ b₁ + μ x ^ b₂ : ℝ)⁻¹ : ℂ) * f.toFun x := by
  sorry

end MasulloGRH
