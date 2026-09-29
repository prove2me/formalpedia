-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal
-- name    : LanglandsTunnell.CubicInduction.exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/4e1c0dd9-27ad-5e5c-8c7d-ac23a761fc95
-- title:
--   Coset system for diag(varpi,varpi,1) and Whittaker coset sums
-- statement:
--   Let $v$ be a height one prime of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_v$ for the completion of $\mathbb Q$ at $v$, let $N =$ `Ideal.absNorm v.asIdeal`, let $\varpi$ be the chosen uniformizer `varpi v` of $F$, and let $U =$ `localMaximalCompact3 (𝓞 ℚ) ℚ v` be the subgroup of those $k \in \mathrm{GL}_3(F)$ all of whose entries and all of whose entries of $k^{-1}$ have valuation $\le 1$. The assertion is that there is a family $y : \mathrm{Fin}(N^2+N+1) \to \mathrm{GL}_3(F)$ with two properties. First, $y$ is a Hecke coset system for $U$ and $g =$ `heckeGen2 v` $= \mathrm{diag}(\varpi,\varpi,1)$: each $y_i$ lies in the double coset $U\,g\,U$, every element of $U\,g\,U$ lies in $y_iU$ for some $i$, and $i \mapsto y_iU$ is injective. Second, for every additive character $\psi_v$ of $F$ with values in $\mathbb C$ that is trivial on $\{x : |x|_v \le 1\}$, every $W : \mathrm{GL}_3(F) \to \mathbb C$ satisfying $W\bigl(n(x,y,z)\,h\bigr) = \psi_v(x+y)\,W(h)$ for all $x,y,z \in F$ and $h \in \mathrm{GL}_3(F)$, where $n(x,y,z)$ is the upper unipotent matrix with entries $x,y,z$ in positions $(1,2),(2,3),(1,3)$, and all natural numbers $k_1 \ge k_2$, one has, writing $t(k_1,k_2)$ for the point `twoRowPointLocal v k₁ k₂`, namely the image under the block embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$ (with $1$ in the last diagonal slot) of $\mathrm{diag}(\pi^{k_1}, \pi^{k_2})$ for the unit $\pi =$ `ratPrimeUnit v` of $F$, and $c' =$ `centralGen v` $\cdot$ `(heckeGen2 v)⁻¹` $= \mathrm{diag}(\varpi,\varpi,\varpi)\,\mathrm{diag}(\varpi,\varpi,1)^{-1}$:
--   $$\sum_i W\bigl(t(k_1,k_2)\,y_i\bigr) = N^2\,W\bigl(t(k_1+1,k_2+1)\bigr) + N\,W\bigl(t(k_1+1,k_2)\,c'\bigr) + W\bigl(t(k_1,k_2+1)\,c'\bigr),$$
--   the coefficients being the complex numbers `cNormQ v ^ 2` and `cNormQ v` attached to $N$.
--
--   This is the local computation of the second spherical Hecke operator at $v$ (the double coset of $\mathrm{diag}(\varpi,\varpi,1)$, of index $N^2+N+1$) acting on a $\psi_v$-Whittaker function, evaluated at the dominant torus points $\mathrm{diag}(\pi^{k_1},\pi^{k_2},1)$ with $k_1 \ge k_2$. It is used in [`LanglandsTunnell.CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace`](thm.html#LanglandsTunnell.CubicInduction.exists_isGL3PsiWhittakerFn_isInducedSphericalAt_of_not_isBadPlace) and in [`LanglandsTunnell.CubicInduction.sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn`](thm.html#LanglandsTunnell.CubicInduction.sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn), where the resulting recursion determines the torus values of a Hecke eigenfunction on $\mathrm{GL}_3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_isHeckeCosetSystem_heckeGen2_cosetSum_twoRowPointLocal
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal ^ 2 + Ideal.absNorm v.asIdeal + 1) → LocalGL3 v,
      HeckeIntegralSeam.IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) reps ∧
      ∀ (ψv : AddChar (v.adicCompletion ℚ) ℂ), (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1) →
        ∀ W : LocalGL3 v → ℂ, IsGL3PsiWhittakerFn ψv W →
            ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ →
              cosetSum reps W (twoRowPointLocal v k₁ k₂) =
                cNormQ v ^ 2 * W (twoRowPointLocal v (k₁ + 1) (k₂ + 1)) +
                cNormQ v * W (twoRowPointLocal v (k₁ + 1) k₂ * (centralGen v * (heckeGen2 v)⁻¹)) +
                W (twoRowPointLocal v k₁ (k₂ + 1) * (centralGen v * (heckeGen2 v)⁻¹)) := by sorry
