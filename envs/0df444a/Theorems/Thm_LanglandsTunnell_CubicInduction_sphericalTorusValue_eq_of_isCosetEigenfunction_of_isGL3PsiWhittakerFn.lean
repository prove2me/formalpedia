-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/ccc5b866-f821-506d-ad07-f59bdd1fa737
-- title:
--   Torus values of a spherical GL₃ Whittaker function
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), let $\psi_v$ be an additive character of the completion $\mathbb{Q}_v$ with values in $\mathbb{C}$, let $W$ be a function on $\mathrm{GL}_3(\mathbb{Q}_v)$ with complex values, and let $e_1,e_2,e_3\in\mathbb{C}$. Write $K$ for `localMaximalCompact3`, the subgroup of those $k\in\mathrm{GL}_3(\mathbb{Q}_v)$ all of whose entries and all of whose entries of $k^{-1}$ have valuation $\le 1$, write $q=$ `cNormQ v` for the absolute norm of the ideal of $v$ viewed in $\mathbb{C}$, and write $\varpi$ for the uniformiser `varpi v`. Four hypotheses are assumed on $W$: it is right invariant under $K$, i.e. $W(gu)=W(g)$ for all $g$ and all $u\in K$; it is a coset eigenfunction for $K$ and the element `heckeGen1` $=\mathrm{diag}(\varpi,1,1)$ with eigenvalue $q\,e_1$, meaning that for every finite family of representatives `reps` satisfying [`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15) for $K$ and that element, $\sum_i W(g\cdot \mathrm{reps}_i)=q\,e_1\,W(g)$ for all $g$; it is likewise a coset eigenfunction for `heckeGen2` $=\mathrm{diag}(\varpi,\varpi,1)$ with eigenvalue $q\,e_2$; and $W(\mathrm{diag}(\varpi,\varpi,\varpi)\,g)=e_3\,W(g)$ for all $g$. Further, $W$ is a $\psi_v$-Whittaker function: $W\bigl(u(x,y,z)g\bigr)=\psi_v(x+y)\,W(g)$ for all $x,y,z\in\mathbb{Q}_v$ and all $g$, where $u(x,y,z)$ is the upper unipotent matrix with entries $x,y$ above the diagonal and $z$ in the corner; the character $\psi_v$ is trivial on the set of $x$ with valuation $\le 1$, and there is some $x$ with valuation $\le 1$ for which $\psi_v(\varpi^{-1}x)\ne 1$. Let $h_n=$ `sphericalTorusValue` $e_1\,e_2\,e_3\,n$ be given by $h_0=1$, $h_1=e_1$, $h_2=e_1^2-e_2$ and $h_{n+3}=e_1h_{n+2}-e_2h_{n+1}+e_3h_n$. The conclusion is twofold: first, for every $n\in\mathbb{N}$, $W(\mathrm{iotaTorusLocal}\;v\;n)=W(1)\,q^{-n}h_n$, where `iotaTorusLocal v n` is the image under the block embedding `iotaGL` of $\mathrm{GL}_2(\mathbb{Q}_v)$ into $\mathrm{GL}_3(\mathbb{Q}_v)$ of `diagHom (ratPrimeUnit v ^ n)`; second, for all $k_1,k_2\in\mathbb{N}$ with $k_2+1\le k_1$, $$W(\mathrm{twoRowPointLocal}\;v\;k_1\;(k_2+1))=W(1)\,q^{-k_1}\bigl(h_{k_1}h_{k_2+1}-h_{k_1+1}h_{k_2}\bigr),$$ where `twoRowPointLocal v k₁ k₂` is the image under `iotaGL` of `diagUnits2 (ratPrimeUnit v ^ k₁) (ratPrimeUnit v ^ k₂)`.
--
--   This is the unramified evaluation of a spherical Whittaker function on $\mathrm{GL}_3$ over a $p$-adic field — Shintani's explicit formula — stated for an abstract triple $(e_1,e_2,e_3)$ of complex Hecke data rather than for Satake parameters of a given representation, the values at one-row and two-row torus points being expressed through the sequence $h_n$ attached to $X^3-e_1X^2+e_2X-e_3$. It is used to show that a Whittaker function vanishing at the identity vanishes identically, to compute $W$ along the powers of the embedded torus, and to identify the Laurent expansion of the local zeta integral with the $\mathrm{GL}_3$ $L$-factor polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.sphericalTorusValue_eq_of_isCosetEigenfunction_of_isGL3PsiWhittakerFn
    (v : HeightOneSpectrum (𝓞 ℚ)) (ψv : AddChar (v.adicCompletion ℚ) ℂ) (W : LocalGL3 v → ℂ) (e₁ e₂ e₃ : ℂ)
    (hW : IsRightInvariant (localMaximalCompact3 (𝓞 ℚ) ℚ v) W ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen1 v) W (cNormQ v * e₁) ∧
      IsCosetEigenfunction (localMaximalCompact3 (𝓞 ℚ) ℚ v) (heckeGen2 v) W (cNormQ v * e₂) ∧
      ∀ g : LocalGL3 v, W (centralGen v * g) = e₃ * W g)
    (hψ : IsGL3PsiWhittakerFn ψv W)
    (hψ0 : ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → ψv x = 1)
    (hψ1 : ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ ψv ((varpi v)⁻¹ * x) ≠ 1) :
    (∀ n : ℕ, W (iotaTorusLocal v n) = W 1 * ((cNormQ v)⁻¹ ^ n * sphericalTorusValue e₁ e₂ e₃ n)) ∧
    (∀ k₁ k₂ : ℕ, k₂ + 1 ≤ k₁ → W (twoRowPointLocal v k₁ (k₂ + 1)) =
      W 1 * ((cNormQ v)⁻¹ ^ k₁ *
        (sphericalTorusValue e₁ e₂ e₃ k₁ * sphericalTorusValue e₁ e₂ e₃ (k₂ + 1) -
          sphericalTorusValue e₁ e₂ e₃ (k₁ + 1) * sphericalTorusValue e₁ e₂ e₃ k₂))) := by sorry
