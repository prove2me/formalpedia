-- Prove2me | Theorems.Thm_MasulloGRH_tateIdeleDomain_relCompact_and_interior_nonempty
-- name    : MasulloGRH.tateIdeleDomain_relCompact_and_interior_nonempty
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:23:36.579622+00:00
-- url     : https://prove2.me/theorems/cae03999-3623-40c3-9c13-eecdd09d0c5f
-- title:
--   Proposition A.2.3.10(1) — Tate's idelic domain $E_F^1$ lies in the norm-one ideles, where it is relatively compact with non-empty interior
-- statement:
--   **Tate's idelic domain $E_F^1$ is relatively compact with non-empty interior in the norm-one ideles** (Proposition A.2.3.10(1) of the source, with the inclusion $E_F^1\subset\mathrm{GL}_1(\mathbb A_F)^1$ of (A.2.3.14)).
--
--   Let $F$ be a number field, $\mathbb I_F=\mathrm{GL}_1(\mathbb A_F)$ its idele group with the idele topology, $|g|_F=\prod_v|g_v|_v$ the idelic norm and $\mathbb I_F^1=\{g:\ |g|_F=1\}$ the group of norm-one ideles, with the topology induced from $\mathbb I_F$; $F^\times$ is embedded diagonally in $\mathbb I_F^1$. Let $E_0\subset\mathbb I_\infty^1$ be Tate's archimedean domain (Definition A.2.3.6, built from a $\mathbb Z$-basis of $\mathcal O_F^\times/\mu_F$, an archimedean place $v_0$ and an identification $\iota_{v_0}$ of $F_{v_0}$ with $\mathbb R$ or $\mathbb C$), let $\widehat{\mathcal O}_F^\times=\prod_{v\nmid\infty}\mathcal O_{F_v}^\times$, and let $g_1=1,g_2,\dots,g_{h_F}\in\mathbb I_F^1$ be ideles whose ideal classes $\big[\prod_{\mathfrak p}\mathfrak p^{\operatorname{ord}_{\mathfrak p}(g_{i,\mathfrak p})}\big]$ are the $h_F$ distinct elements of the ideal class group $\mathrm{Pic}(\mathcal O_F)$. Tate's idelic fundamental domain is
--   $$E_F^1=\bigcup_{i=1}^{h_F}g_i\,\big(E_0\times\widehat{\mathcal O}_F^\times\big)\subset\mathbb I_F,$$
--   where $E_0\times\widehat{\mathcal O}_F^\times$ is the set of ideles with archimedean part in $E_0$ and finite part in $\widehat{\mathcal O}_F^\times$ (`MasulloGRH.tateIdeleDomain`).
--
--   Then:
--
--   1. $E_F^1\subset\mathbb I_F^1$;
--   2. the closure of $E_F^1$ in $\mathbb I_F^1$ is compact;
--   3. the interior of $E_F^1$ in $\mathbb I_F^1$ is non-empty.
--
--   Together with Proposition A.2.3.10(2) this says that $E_F^1$ is a relatively compact fundamental domain, with non-empty interior, for the discrete subgroup $F^\times$ of $\mathbb I_F^1$; in particular it re-proves that the norm-one idele class group $C_F^1=\mathbb I_F^1/F^\times$ is compact, and it gives $E_F^1$ finite positive Haar measure (the volume of $C_F^1$; cf. eq. (A.3.2.1) of the source, where it is expressed through the class number, the regulator, the number of roots of unity and the discriminant of $F$).
--
--   **Formalization Note.** $\mathbb I_F$ is `MasulloGRH.IdeleGroup F = (AdeleRing (𝓞 F) F)ˣ` with the units topology, $|\cdot|_F$ is the platform's `MasulloGRH.ideleNorm`, and $\mathbb I_F^1$ is the subtype `{g // ideleNorm g = 1}` with the subspace topology. The representatives are a map `r : ClassGroup (𝓞 F) → IdeleGroup F` with the hypotheses `r 1 = 1` ($g_1=1$), `ideleNorm (r c) = 1` and `ideleIdealClass F (r c) = c` (the $g_i$ have norm one and represent the classes). The statement is asserted for every basis `b`, place `v₀` and `σ ∈ Aut_ℝ(ℂ)` entering $E_0$. The closure and the interior are those of the subset $\{g\in\mathbb I_F^1:\ g\in E_F^1\}$ of the subtype $\mathbb I_F^1$ (in $\mathbb I_F$ itself the interior of $E_F^1$ is empty).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 552, Proposition A.2.3.10(1) (with Definition A.2.3.6, eq. (A.2.3.14), p. 549); classical reference for the domain (cited in Remark A.2.3.7, p. 549): J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, Def. 4.3.2; general references given by the paper for §A.2 (p. 545): D. Ramakrishnan, R.J. Valenza, Fourier Analysis on Number Fields, Springer, Ch. 5, §5.1; J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, §4.1, §4.3

import Mathlib
import Definitions.Def_MasulloGRH_TateIdeleDomain

open NumberField IsDedekindDomain

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace MasulloGRH

theorem tateIdeleDomain_relCompact_and_interior_nonempty
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (r : ClassGroup (𝓞 F) → IdeleGroup F)
    (hr₁ : r 1 = 1) (hrn : ∀ c : ClassGroup (𝓞 F), ideleNorm (r c) = 1)
    (hr : ∀ c : ClassGroup (𝓞 F), ideleIdealClass F (r c) = c) :
    tateIdeleDomain F b v₀ σ r ⊆ {g | ideleNorm g = 1} ∧
    IsCompact (closure
      {g : {g : IdeleGroup F // ideleNorm g = 1} | g.val ∈ tateIdeleDomain F b v₀ σ r}) ∧
    (interior
      {g : {g : IdeleGroup F // ideleNorm g = 1} |
        g.val ∈ tateIdeleDomain F b v₀ σ r}).Nonempty := by sorry

end MasulloGRH
