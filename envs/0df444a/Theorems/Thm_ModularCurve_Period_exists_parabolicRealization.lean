-- Prove2me | Theorems.Thm_ModularCurve_Period_exists_parabolicRealization
-- name    : ModularCurve.Period.exists_parabolicRealization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/6d281dea-c629-5b26-889c-4c70f0c94987
-- title:
--   Nonzero parabolic realisation of a normalised eigenform over k
-- statement:
--   Let $N$ be a nonzero natural number, let $f$ be a weight-two cusp form for $\Gamma_0(N)$, and assume (i) `hf`: $f$ is a normalised eigenform in the sense that its $q$-expansion coefficients $a_n =$ `qCoeff f n` satisfy $a_1 = 1$, $a_{mn} = a_m a_n$ for coprime $m,n$, $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^{r}}$ for primes $p \nmid N$, and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for primes $p \mid N$; and (ii) `hint`: for every prime $\ell$ the coefficient $a_\ell$ lies in the image of the integral closure $\overline{\mathbb{Z}}$ of $\mathbb{Z}$ in $\mathbb{C}$, so that a lift [`CuspForm.eigenLift hint ℓ`](def/CuspForm_EigenformCoefficientRing.html#L19) $\in \overline{\mathbb{Z}}$ of $a_\ell$ is available. Let $k$ be a field and $\mathrm{red} : \overline{\mathbb{Z}} \to k$ a ring homomorphism. Then there is an additive homomorphism $f_0 : \mathrm{Additive}(\Gamma_0(N)) \to k$ which is parabolic, i.e. lies in the $k$-submodule `parabolicHoms` of homomorphisms vanishing on every $\gamma$ whose matrix has trace squared equal to $4$, such that $f_0 \neq 0$ and, for every prime $\ell$, the Hecke operator [`HeckeEis.heckeOperatorHom N ℓ k`](def/Gamma0HeckeOperatorHom.html#L285) (pullback along the conjugation map `heckeConj N ℓ` followed by corestriction from the subgroup `heckeUpper N ℓ`) sends $f_0$ to $\mathrm{red}(\mathrm{eigenLift}\ \mathrm{hint}\ \ell) \cdot f_0$. The eigenvalue condition is asserted for all primes $\ell$, including those dividing $N$.
--
--   This is the realisation of a normalised weight-two eigenform as a nonzero Hecke eigenvector in parabolic cohomology of $\Gamma_0(N)$ with coefficients in a field $k$, obtained by reducing the period map of $f$ along a chosen homomorphism $\overline{\mathbb{Z}} \to k$. It is used in the level-raising analysis, specifically by [`LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime`](thm.html#LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime), to transfer eigenvalue congruences from the complex eigenform to a mod-$\mathfrak{m}$ eigenvector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_Period_exists_parabolicRealization.lean

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CuspForm_EigenformCoefficientRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup

theorem ModularCurve.Period.exists_parabolicRealization (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : f.IsNormalizedEigenform)
    (hint : f.PrimeCoeffsIntegral)
    (k : Type) [Field k] (red : integralClosure ℤ ℂ →+* k) :
    ∃ f₀ : ModularCurve.Period.parabolicHoms k (Gamma0 N) k, f₀ ≠ 0 ∧
      ∀ (ℓ : ℕ) (_ : NeZero ℓ) (hℓp : ℓ.Prime),
        HeckeEis.heckeOperatorHom N ℓ k (f₀ : Additive (Gamma0 N) →+ k) =
          (red (CuspForm.eigenLift hint ⟨ℓ, hℓp⟩)) •
            (f₀ : Additive (Gamma0 N) →+ k) := by sorry
