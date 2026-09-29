-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum
-- name    : LanglandsTunnell.CubicInduction.exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/b3b872b5-b788-5566-8cb4-a2e17c07bc8e
-- title:
--   Truncated Jacquet integrals of a flat cell-section family
-- statement:
--   Fix a nonzero prime $p$ of $\mathcal O_{\mathbb Q}$, with completion $\mathbb Q_p$ and residue norm $N=\mathrm{absNorm}(p)$. Let $\lambda_0,\lambda_1,\lambda_2$ be homomorphisms $\mathbb Q_p^\times\to\mathbb C^\times$, each locally constant, let $n\in\mathbb Z^3$, and let $u\mapsto\lambda_u=(\lambda_{u,0},\lambda_{u,1},\lambda_{u,2})$ be a family of such homomorphisms indexed by $u\in\mathbb C$ whose values are prescribed by $\lambda_{u,i}(a)=\lambda_i(a)\,\|a\|^{n_iu}$ for all $a\in\mathbb Q_p^\times$. Let $\Phi:\mathbb Q_p^3\to\mathbb C$ be locally constant with compact support, let $g\in GL_3(\mathbb Q_p)$ and let $c\in\mathbb Z$. The assertion is that there is a function $e:\mathbb Z\to\mathbb C$ with $\{i: e_i\neq 0\}$ finite such that for every $u\in\mathbb C$ the truncated Jacquet integral at level $c$ of the right translate $h\mapsto f_{\lambda_u,\Phi}(hg)$, namely $$\int_{\mathrm v(x)\le N^{c},\ \mathrm v(y)\le N^{c},\ \mathrm v(z)\le N^{2c}}\psi_p\bigl(-(x+y)\bigr)\,f_{\lambda_u,\Phi}\bigl(w_0\,n(x,y,z)\,g\bigr)\,dx\,dy\,dz,$$ taken against the triple self-dual Haar measure, with $w_0$ the antidiagonal permutation matrix, $n(x,y,z)$ the upper unipotent matrix and $\psi_p$ the standard local additive character, equals the finite sum $\sum_{i\in\mathbb Z}N^{-iu}e_i$. Here $f_{\lambda_u,\Phi}$ is the cell section: it vanishes off the big cell $\{\,\mathrm{cornerEntry}\neq 0,\ \mathrm{lowerMinor}\neq 0\,\}$, and on that cell its value at $h$ is $\lambda_{u,0}(\det h/\mathrm{lowerMinor})\,\lambda_{u,1}(\mathrm{lowerMinor}/\mathrm{cornerEntry})\,\lambda_{u,2}(\mathrm{cornerEntry})\cdot\bigl(\|\det h/\mathrm{lowerMinor}\|/\|\mathrm{cornerEntry}\|\bigr)$ times $\Phi$ evaluated at the cell ratio $(h_{21}/\mathrm{cornerEntry},\,h_{22}/\mathrm{cornerEntry},\,\mathrm{outerMinor}/\mathrm{lowerMinor})$. The coefficients $e_i$ do not depend on $u$.
--
--   This is the level-by-level form of the flatness statement for local Whittaker integrals of principal-series sections of $GL_3(\mathbb Q_p)$: along the family obtained by twisting the inducing quasi-characters by $\|\cdot\|^{n_iu}$, each truncated Jacquet integral is a finite exponential sum in $N^{-u}$ with $u$-independent coefficients. It is used in [`LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_twistFamily_eq_finsum_and_forall_le_jacquetTruncated3_eq`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_twistFamily_eq_finsum_and_forall_le_jacquetTruncated3_eq), where an eventual-constancy argument upgrades it to the stabilised Whittaker value at a level independent of $u$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

open scoped Classical

theorem LanglandsTunnell.CubicInduction.exists_forall_jacquetTruncated3_cellSectionOf_twistFamily_eq_finsum
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))

    (n : Fin 3 → ℤ)
    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u i a : ℂˣ) : ℂ) = ((lam i a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ ((n i : ℂ) * u))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ)
    (g : LocalGL3 p) (c : ℤ) :
    ∃ e : ℤ → ℂ, {i : ℤ | e i ≠ 0}.Finite ∧
      ∀ u : ℂ, jacquetTruncated3 p c (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf p (lamU u) Φ)) =
        ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * e i := by sorry
