-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_twistFamily_eq_finsum_and_forall_le_jacquetTruncated3_eq
-- name    : LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_twistFamily_eq_finsum_and_forall_le_jacquetTruncated3_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/7a9b1ca5-7a7c-58c1-ab27-5340a5bf7482
-- title:
--   Flat families of stabilised GL₃ Jacquet–Whittaker functions
-- statement:
--   Let $p$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, with completion $\mathbb{Q}_p :=$ `p.adicCompletion ℚ`. Given three locally constant homomorphisms $\lambda_i : \mathbb{Q}_p^{\times} \to \mathbb{C}^{\times}$, integer slopes $n : \mathrm{Fin}\,3 \to \mathbb{Z}$, and a family $\lambda_u$ of triples of such homomorphisms indexed by $u \in \mathbb{C}$ satisfying $\lambda_u(i)(a) = \lambda_i(a)\,\lVert a\rVert^{n_i u}$ for all $u$, $i$, $a$, and given $\Phi : \mathbb{Q}_p^3 \to \mathbb{C}$ locally constant with compact support, the assertion is the existence of coefficient functions $E_i : GL_3(\mathbb{Q}_p) \to \mathbb{C}$, $i \in \mathbb{Z}$, independent of $u$, with the following three properties. First, for every compact $C \subseteq GL_3(\mathbb{Q}_p)$ the set of indices $i$ for which $E_i$ is non-zero at some point of $C$ is finite. Second, for all $u \in \mathbb{C}$ and all $g \in GL_3(\mathbb{Q}_p)$ one has $\mathrm{jacquetWhittaker3}$ of $(\lambda_u, \Phi)$ at $g$ equal to the finite sum $\sum_{i \in \mathbb{Z}} \mathrm{absNorm}(p)^{-iu} E_i(g)$, where the Jacquet–Whittaker function at $g$ is the truncated Jacquet integral, at the level `jacquetLevel`, of the right translate by $g$ of the big-cell section `cellSectionOf p (lamU u) Φ` (the indicator of the locus where the corner entry and the lower $2\times2$ minor are non-zero, times `cellValue` of $\lambda_u$ times $\Phi$ of `cellRatio`). Third, for every $g$ there is $c_0 \in \mathbb{N}$, independent of $u$, such that for all $u \in \mathbb{C}$ and all integers $c \ge c_0$ the truncated integral $\mathrm{jacquetTruncated3}\,p\,c$ of that right translate — the integral of $\psi_p(-(x+y))$ against the value of the translate at $w_3 \cdot u_3(x,y,z)$ over the ball $v(x), v(y) \le \exp c$, $v(z) \le \exp(2c)$ for the product of self-dual Haar measures — already equals the Jacquet–Whittaker value at $g$.
--
--   This is the flatness and stabilisation statement for Whittaker functions attached to principal-series data on $GL_3(\mathbb{Q}_p)$ twisted along a line $\lVert\cdot\rVert^{n_i u}$: the truncated Jacquet integrals stabilise at a level independent of the twist parameter, and the resulting Whittaker function is a finite Laurent-type exponential sum in $\mathrm{absNorm}(p)^{-u}$ with $u$-free coefficients, locally uniformly in $g$. It supplies the holomorphy and finiteness input for the deformation argument establishing the local $GL_3 \times GL_2$ Rankin–Selberg functional equation, and is cited there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_twistFamily_eq_finsum_and_forall_le_jacquetTruncated3_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

open scoped Classical

theorem LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_twistFamily_eq_finsum_and_forall_le_jacquetTruncated3_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (lam : Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (hlam : ∀ i, IsLocallyConstant (lam i))

    (n : Fin 3 → ℤ)
    (lamU : ℂ → Fin 3 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (hlamU : ∀ (u : ℂ) (i : Fin 3) (a : (p.adicCompletion ℚ)ˣ),
      ((lamU u i a : ℂˣ) : ℂ) = ((lam i a : ℂˣ) : ℂ) * ((‖(a : p.adicCompletion ℚ)‖ : ℂ)) ^ ((n i : ℂ) * u))
    (Φ : (Fin 3 → p.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    ∃ E : ℤ → LocalGL3 p → ℂ,
      (∀ C : Set (LocalGL3 p), IsCompact C → {i : ℤ | ∃ g ∈ C, E i g ≠ 0}.Finite) ∧
      (∀ (u : ℂ) (g : LocalGL3 p),
        jacquetWhittaker3 p (lamU u) Φ g = ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * u) * E i g) ∧
      (∀ g : LocalGL3 p, ∃ c₀ : ℕ, ∀ (u : ℂ) (c : ℤ), (c₀ : ℤ) ≤ c →
        jacquetTruncated3 p c (gl3AmbientRightTranslate (R := ℂ) g (cellSectionOf p (lamU u) Φ)) =
          jacquetWhittaker3 p (lamU u) Φ g) := by sorry
