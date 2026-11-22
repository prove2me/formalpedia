-- Prove2me | Theorems.Thm_MasulloGRH_ideleGroup_oneParameterSubgroup_finite_component_and_norm
-- name    : MasulloGRH.ideleGroup_oneParameterSubgroup_finite_component_and_norm
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T16:39:34.794795+00:00
-- url     : https://prove2.me/theorems/488503ec-88ad-4dac-9021-98b26d8fd2b4
-- title:
--   Lemma 2.2.4.1 — a continuous one-parameter subgroup $\gamma\colon\mathbb R_{>0}\to\mathrm{GL}_1(\mathbb A_F)$ is trivial at the finite places, and $|\gamma(t)|_F=t^{\alpha}$ for a unique real $\alpha$
-- statement:
--   **Continuous one-parameter subgroups of the idele group** (Lemma 2.2.4.1 of the source).
--
--   Let $F$ be a number field and $\mathrm{GL}_1(\mathbb A_F)=\mathrm{GL}_1(\mathbb A_{F,S_\infty})\times\mathrm{GL}_1(\mathbb A_F^f)$ its idele group with the idelic topology, the product of the archimedean ideles $\prod_{w\mid\infty}F_w^\times$ and the finite ideles. Let $|g|_F=\prod_v|g_v|_v$ be the idelic norm. Let
--   $$\gamma\colon\mathbb R_{>0}\to\mathrm{GL}_1(\mathbb A_F)$$
--   be a continuous one-parameter subgroup, i.e. a continuous homomorphism from the multiplicative group of positive real numbers.
--
--   Then:
--
--   1. $\gamma$ takes values in the archimedean ideles: the finite component of $\gamma(t)$ is $1$ for every $t>0$, that is,
--   $$\gamma(\mathbb R_{>0})\subset\mathrm{GL}_1(\mathbb A_{F,S_\infty})\times\{1\};$$
--   2. there is a unique real number $\alpha$ such that $|\gamma(t)|_F=t^{\alpha}$ for all $t>0$.
--
--   Consequently exactly one of the following holds: either $\alpha\ne0$ and $|\cdot|_F\circ\gamma$ is an automorphism $t\mapsto t^\alpha$ of $\mathbb R_{>0}$, or $\alpha=0$ and $\gamma$ takes values in the norm-one archimedean ideles $\mathrm{GL}_1(\mathbb A_{F,S_\infty})^1\times\{1\}$; this is the dichotomy as printed in the source.
--
--   The source uses the lemma to define directional derivatives $\partial_\gamma$ of Schwartz–Bruhat functions and of adelic $\theta$-functions along one-parameter subgroups of ideles, e.g. along a section of the idelic norm ($\alpha=1$).
--
--   **Formalization Note.** $\mathbb R_{>0}$ is the subtype `{t : ℝ // 0 < t}` with Mathlib's multiplicative group structure, and $\gamma$ is a monoid homomorphism into the platform type `MasulloGRH.IdeleGroup F` (the unit group of the adele ring with the unit topology), assumed continuous. Item 1 says that the second component of the adele $\gamma(t)$ is $1$; item 2 uses the real power `Real.rpow`. The two cases of the source correspond to $\alpha\ne0$ and $\alpha=0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 86–87, Lemma 2.2.4.1, eq. (2.2.4.1)

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem ideleGroup_oneParameterSubgroup_finite_component_and_norm
    (F : Type*) [Field F] [NumberField F]
    (γ : {t : ℝ // 0 < t} →* IdeleGroup F) (hγ : Continuous γ) :
    (∀ t : {t : ℝ // 0 < t}, ((γ t : IdeleGroup F) : AdeleRing (𝓞 F) F).2 = 1) ∧
    ∃! α : ℝ, ∀ t : {t : ℝ // 0 < t}, ideleNorm (γ t) = (t : ℝ) ^ α := by sorry

end MasulloGRH
