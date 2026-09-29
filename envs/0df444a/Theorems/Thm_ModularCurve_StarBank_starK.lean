-- Prove2me | Theorems.Thm_ModularCurve_StarBank_starK
-- name    : ModularCurve.StarBank.starK
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/43a91ee6-8546-5654-8b64-6c03f3e8a430
-- title:
--   Characteristic ℓ: a unit identity G(j)Δ^M = 1
-- statement:
--   Let $K$ be a field, $\ell$ a prime, and suppose $K$ has characteristic $\ell$ (as a `CharP` instance). Work inside the Laurent series ring `LaurentSeries K` with the two distinguished elements built from integral $q$-expansions: $j$, given by `jqModC K`, namely $q^{-1}$ (the Hahn series `single (-1) 1`) times the power series `jNum` $= E_4^3\cdot(\eta\text{-unit})^{-1}$ with its coefficients read in $K$, where $E_4$ is `eisenstein4`, the series with constant term $1$ and $n$-th coefficient $240\sigma_3(n)$, and $(\eta\text{-unit})^{-1}$ is the power-series inverse of `etaProd`$^{24} = \prod_{n\ge 1}(1-q^n)^{24}$; and the discriminant $\Delta$, given by $q\cdot\big(\prod_{n\ge1}(1-q^n)\big)^{24}$, i.e. `single 1 1` times the $24$th power of the image of `etaProd` in $K$. The single hypothesis is conditional: if $5\le\ell$, there are a power series $T\in\mathbb{Z}[[q]]$ and a polynomial $G\in\mathbb{Z}[X]$ such that $\ell$ divides every coefficient of $T$ of index $\ge 1$, $\ell$ does not divide the constant coefficient of $T$, $G$ has degree $\ell-1$ with $(\ell-1)$-st coefficient equal to that constant coefficient, and the identity $T = G(j)\,\Delta^{\ell-1}$ holds in `LaurentSeries ℤ` (with $j$ and $\Delta$ formed over $\mathbb{Z}$ as above). The conclusion is that there exist a natural number $M$ with $1\le M$ whose image in $K$ is nonzero, and a polynomial $G\in K[X]$ of degree exactly $M$, such that $G(j)\cdot\Delta^{M} = 1$ in `LaurentSeries K`, the evaluation being `Polynomial.aeval` at `jqModC K`.
--
--   The hypothesis packages, for $\ell\ge 5$, the reduction modulo $\ell$ of the classical congruence for the Eisenstein series of weight $\ell-1$ (the Hasse invariant), expressed entirely in terms of $q$-expansions: $E_{\ell-1} = G(j)\Delta^{\ell-1}$ with $G$ of degree $\ell-1$. Unlike the textbook formulation, nothing here concerns modular forms or the curve $X_0(N)$ as such: all objects are formal Laurent series, and the output is a purely formal unit identity saying that $\Delta^{-M}$ is a polynomial in $j$ of degree $M$ with $M$ invertible in $K$. The identity is used in the proof that $j(q^p)$ does not lie in $K(j(q))$ for a prime $p\ne\ell$ ([`ModularCurve.StarBank.starBank`](thm.html#ModularCurve.StarBank.starBank)), where the finitely many roots of $G$ supply the $j$-values on which the characteristic-$\ell$ argument is run and the invertibility of $M$ in $K$ is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_StarBank_starK.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries PowerSeries ModularCurve

theorem ModularCurve.StarBank.starK (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hHasse : 5 ≤ ℓ → ∃ (T : PowerSeries ℤ) (G : Polynomial ℤ),
        (∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) ∧ ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T
        ∧ G.natDegree = ℓ - 1 ∧ G.coeff (ℓ - 1) = PowerSeries.constantCoeff T
        ∧ HahnSeries.ofPowerSeries ℤ ℤ T
            = Polynomial.aeval (jqModC ℤ) G
              * (HahnSeries.single (1 : ℤ) (1 : ℤ)
                  * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) ^ (ℓ - 1)) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : K) ≠ 0 ∧ ∃ G : Polynomial K, G.natDegree = M
      ∧ Polynomial.aeval (jqModC K) G
          * (HahnSeries.single (1 : ℤ) (1 : K)
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 := by sorry
