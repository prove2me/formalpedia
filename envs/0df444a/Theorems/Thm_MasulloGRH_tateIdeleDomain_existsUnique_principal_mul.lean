-- Prove2me | Theorems.Thm_MasulloGRH_tateIdeleDomain_existsUnique_principal_mul
-- name    : MasulloGRH.tateIdeleDomain_existsUnique_principal_mul
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:23:01.166402+00:00
-- url     : https://prove2.me/theorems/e6104f91-b563-40c4-bd89-6e751e7c97ed
-- title:
--   Proposition A.2.3.10(2) — every norm-one idele is $\xi e$ for a unique $\xi\in F^\times$ and $e\in E_F^1$ (Tate's fundamental domain)
-- statement:
--   **Tate's idelic domain $E_F^1$ is a strict fundamental domain for $F^\times$ acting on the norm-one ideles** (Proposition A.2.3.10(2), eqs. (A.2.3.25)–(A.2.3.26) of the source).
--
--   Let $F$ be a number field, $\mathbb I_F=\mathrm{GL}_1(\mathbb A_F)$ its idele group with the idele topology, $|g|_F=\prod_v|g_v|_v$ the idelic norm and $\mathbb I_F^1=\{g:\ |g|_F=1\}$ the group of norm-one ideles, with the topology induced from $\mathbb I_F$; $F^\times$ is embedded diagonally in $\mathbb I_F^1$. Let $E_0\subset\mathbb I_\infty^1$ be Tate's archimedean domain (Definition A.2.3.6, built from a $\mathbb Z$-basis of $\mathcal O_F^\times/\mu_F$, an archimedean place $v_0$ and an identification $\iota_{v_0}$ of $F_{v_0}$ with $\mathbb R$ or $\mathbb C$), let $\widehat{\mathcal O}_F^\times=\prod_{v\nmid\infty}\mathcal O_{F_v}^\times$, and let $g_1=1,g_2,\dots,g_{h_F}\in\mathbb I_F^1$ be ideles whose ideal classes $\big[\prod_{\mathfrak p}\mathfrak p^{\operatorname{ord}_{\mathfrak p}(g_{i,\mathfrak p})}\big]$ are the $h_F$ distinct elements of the ideal class group $\mathrm{Pic}(\mathcal O_F)$. Tate's idelic fundamental domain is
--   $$E_F^1=\bigcup_{i=1}^{h_F}g_i\,\big(E_0\times\widehat{\mathcal O}_F^\times\big)\subset\mathbb I_F,$$
--   where $E_0\times\widehat{\mathcal O}_F^\times$ is the set of ideles with archimedean part in $E_0$ and finite part in $\widehat{\mathcal O}_F^\times$ (`MasulloGRH.tateIdeleDomain`).
--
--   Then for every idele $g$ of norm one there is exactly one $\xi\in F^\times$ such that
--   $$g=\xi\,e\qquad\text{for some }e\in E_F^1 .$$
--   Equivalently,
--   $$F^\times E_F^1=\mathbb I_F^1\qquad\text{and}\qquad\xi E_F^1\cap E_F^1=\varnothing\quad\text{for every }\xi\in F^\times,\ \xi\neq1 .$$
--
--   This is the fundamental-domain property of Tate's thesis: it combines Dirichlet's unit theorem (the archimedean domain $E_0$ is a fundamental domain for $\mathcal O_F^\times$ on the norm-one archimedean ideles) with the finiteness of the class group (the decomposition $\mathbb I_F^1=\bigsqcup_ig_iF^\times(\mathbb I_\infty^1\times\widehat{\mathcal O}_F^\times)$). It allows integrals over the compact group $C_F^1=\mathbb I_F^1/F^\times$ to be unfolded to integrals over $E_F^1$, and the paper uses it in this way throughout Chapter 2 and Appendix A.
--
--   **Formalization Note.** $\mathbb I_F$ is `MasulloGRH.IdeleGroup F = (AdeleRing (𝓞 F) F)ˣ` with the units topology, $|\cdot|_F$ is the platform's `MasulloGRH.ideleNorm`, and $\mathbb I_F^1$ is the subtype `{g // ideleNorm g = 1}` with the subspace topology. The representatives are a map `r : ClassGroup (𝓞 F) → IdeleGroup F` with the hypotheses `r 1 = 1` ($g_1=1$), `ideleNorm (r c) = 1` and `ideleIdealClass F (r c) = c` (the $g_i$ have norm one and represent the classes). The statement is asserted for every basis `b`, place `v₀` and `σ ∈ Aut_ℝ(ℂ)` entering $E_0$. The diagonal embedding $F^\times\to\mathbb I_F$ is `MasulloGRH.principalIdele`. The two assertions of the source are stated together as `∃!`: existence of $\xi$ gives $\mathbb I_F^1\subset F^\times E_F^1$ (the reverse inclusion follows from $E_F^1\subset\mathbb I_F^1$, Proposition A.2.3.10(1), and the product formula), and uniqueness of $\xi$ is equivalent to $\xi E_F^1\cap E_F^1=\varnothing$ for $\xi\ne1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 552, Proposition A.2.3.10(2), eqs. (A.2.3.25)–(A.2.3.26); classical reference for the domain (cited in Remark A.2.3.7, p. 549): J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, Def. 4.3.2; general references given by the paper for §A.2 (p. 545): D. Ramakrishnan, R.J. Valenza, Fourier Analysis on Number Fields, Springer, Ch. 5, §5.1; J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, §4.1, §4.3

import Mathlib
import Definitions.Def_MasulloGRH_TateIdeleDomain

open NumberField IsDedekindDomain

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace MasulloGRH

theorem tateIdeleDomain_existsUnique_principal_mul
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (r : ClassGroup (𝓞 F) → IdeleGroup F)
    (hr₁ : r 1 = 1) (hrn : ∀ c : ClassGroup (𝓞 F), ideleNorm (r c) = 1)
    (hr : ∀ c : ClassGroup (𝓞 F), ideleIdealClass F (r c) = c)
    (g : IdeleGroup F) (hg : ideleNorm g = 1) :
    ∃! ξ : Fˣ, ∃ e ∈ tateIdeleDomain F b v₀ σ r, g = principalIdele F ξ * e := by sorry

end MasulloGRH
