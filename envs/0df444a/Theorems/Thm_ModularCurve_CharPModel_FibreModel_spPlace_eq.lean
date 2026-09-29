-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_eq
-- name    : ModularCurve.CharPModel.FibreModel.spPlace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/3fd359bb-9283-5c32-ab7b-4a11edc0c9d7
-- title:
--   Fibre-model independence of the specialisation of places
-- statement:
--   Fix a nonzero level $N$ and a prime $\ell$ with $\ell \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $k = \mathrm{ResidueField}\,A$ has characteristic $\ell$. Let $fm_1, fm_2$ be two terms of `FibreModel N A ℓ k (IsLocalRing.residue A)`, i.e. each consists of subrings $B_{\mathrm{fin}}, B_{\infty}$ of the base change to $\overline{\mathbb{Q}}$ of the full level-$N$ modular function field inside Laurent series, containing the constants from $A$ and respectively $\bar j, \bar j_N$ and $\bar j^{-1}$, integral over the corresponding affine base rings, together with ring homomorphisms $\pi_{\mathrm{fin}}, \pi_{\infty}$ to $\mathrm{modularFunctionFieldC}\,k\,N$ reducing constants by the residue map and sending $\bar j, \bar j_N, \bar j^{-1}$ to the corresponding characteristic-$\ell$ $q$-expansions. Assume each carries a cusp chart $cc_i$: $\bar j_N\bar j^{-N} \in B_\infty$ with $\pi_\infty$-image $j_N j^{-N}$. Let $dataAll$ assign to every nonzero divisor $d \mid N$ a modular polynomial datum (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(d)$ vanishing at $(j, j_d)$), and assume the mod-$\ell$ reduction of $\Phi$ for $d = N$ is separable over $\mathrm{RatFunc}\,k$. Then the two induced maps from places of the base-changed modular function field to places of $\mathrm{modularFunctionFieldC}\,k\,N$, formed with the surjectivity of the residue map, are equal: $fm_1.\mathrm{spPlace} = fm_2.\mathrm{spPlace}$.
--
--   This is the canonicity statement for reduction of places on the level-$N$ modular curve at a residue characteristic prime to $N$: the specialisation of places attached to a fibre model does not depend on the model chosen, only on $A$ and the level. It is used by [`ModularCurve.CharPModel.FibreModel.spPlace_eq_of_surjective`](thm.html#ModularCurve.CharPModel.FibreModel.spPlace_eq_of_surjective), which transfers the statement to general surjective reduction maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_spPlace_eq.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve CharPModel

set_option autoImplicit false

theorem ModularCurve.CharPModel.FibreModel.spPlace_eq
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (fm₁ fm₂ : ModularCurve.CharPModel.FibreModel N A ℓ (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A))
    (cc₁ : fm₁.CuspChart) (cc₂ : fm₂.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A))
        (RatFunc (IsLocalRing.ResidueField A)))).Separable) :
    fm₁.spPlace Ideal.Quotient.mk_surjective dataAll hsep
      = fm₂.spPlace Ideal.Quotient.mk_surjective dataAll hsep := by sorry
