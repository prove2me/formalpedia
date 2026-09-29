-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal
-- name    : LanglandsTunnell.CubicInduction.exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/9e0cd8f4-1891-5950-ab0e-b5094b4a7bc0
-- title:
--   Coset system for diag(varpi,1,1) and three-term Whittaker sum
-- statement:
--   Let $v$ be a height-one prime of $\mathcal O_{\mathbb Q}$, write $F = \mathbb Q_v$ for the $v$-adic completion, $N =$ `Ideal.absNorm v.asIdeal`, and let $U =$ `localMaximalCompact3` be the subgroup of $\mathrm{GL}_3(F)$ consisting of those $k$ all of whose entries and all of whose entries of $k^{-1}$ have valuation $\le 1$. The assertion is that there is a family $\mathrm{reps} : \mathrm{Fin}(N^2+N+1) \to \mathrm{GL}_3(F)$ with two properties. First, it is a Hecke coset system for $U$ and $g =$ `heckeGen1` $= \mathrm{diag}(\varpi,1,1)$, $\varpi$ the chosen uniformiser unit: every $\mathrm{reps}\,i$ lies in the double coset $U g U$, every element of $U g U$ has the same image as some $\mathrm{reps}\,i$ in $\mathrm{GL}_3(F)/U$, and $i \mapsto \mathrm{reps}\,i \cdot U$ is injective. Second, for every additive character $\psi_v$ of $F$ with values in $\mathbb C$ that is trivial on $\{x : |x| \le 1\}$, every $W : \mathrm{GL}_3(F) \to \mathbb C$ satisfying $W\bigl(\mathrm{upperUnipotent3}(x,y,z)\,g\bigr) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in F$ and all $g$, and all natural numbers $k_2 \le k_1$, writing $t(a,b)$ for the image in $\mathrm{GL}_3(F)$ of $\mathrm{diag}(\pi^{a},\pi^{b})$ under the block embedding $\mathrm{GL}_2 \hookrightarrow \mathrm{GL}_3$, where $\pi$ is the unit `ratPrimeUnit v`, one has $$\sum_i W\bigl(t(k_1,k_2)\,\mathrm{reps}\,i\bigr) = N^2\,W\bigl(t(k_1+1,k_2)\bigr) + N\,W\bigl(t(k_1,k_2+1)\bigr) + W\bigl(t(k_1,k_2)\cdot \mathrm{diag}(\varpi,\varpi,\varpi)\,\mathrm{diag}(\varpi,\varpi,1)^{-1}\bigr).$$ No right $U$-invariance of $W$ is assumed.
--
--   This is the local computation of the Hecke operator attached to the double coset of $\mathrm{diag}(\varpi,1,1)$ on a $\psi_v$-Whittaker function of $\mathrm{GL}_3(\mathbb Q_v)$, evaluated at the dominant diagonal points $\mathrm{diag}(\pi^{k_1},\pi^{k_2},1)$ with $k_2 \le k_1$, together with the existence of the $N^2+N+1$ left coset representatives in Hermite normal form. It feeds the determination of the local Whittaker values of an induced representation at the good places and the recursion for the spherical torus values of a coset eigenfunction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_isHeckeCosetSystem_heckeGen1_cosetSum_twoRowPointLocal
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal ^ 2 + Ideal.absNorm v.asIdeal + 1) → LocalGL3 v,
      HeckeIntegralSeam.IsHeckeCosetSystem (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) reps ∧
      ∀ (ψv : AddChar (v.adicCompletion ℚ) ℂ), (∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1) →
        ∀ W : LocalGL3 v → ℂ, IsGL3PsiWhittakerFn ψv W →
            ∀ k₁ k₂ : ℕ, k₂ ≤ k₁ →
              cosetSum reps W (twoRowPointLocal v k₁ k₂) =
                cNormQ v ^ 2 * W (twoRowPointLocal v (k₁ + 1) k₂) +
                cNormQ v * W (twoRowPointLocal v k₁ (k₂ + 1)) +
                W (twoRowPointLocal v k₁ k₂ * (centralGen v * (heckeGen2 v)⁻¹)) := by sorry
