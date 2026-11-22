-- Prove2me | Theorems.Thm_MasulloGRH_tateIdeleDomain_finite_translates
-- name    : MasulloGRH.tateIdeleDomain_finite_translates
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:23:13.722604+00:00
-- url     : https://prove2.me/theorems/e3fb4d19-ee27-4103-a7e4-94714bb1ebe2
-- title:
--   Proposition A.2.3.10(3) — only finitely many $F^\times$-translates of $\overline{E_F^1}$ meet a compact subset of the norm-one ideles
-- statement:
--   **Local finiteness of the $F^\times$-translates of $\overline{E_F^1}$** (Proposition A.2.3.10(3), eq. (A.2.3.27) of the source).
--
--   Let $F$ be a number field, $\mathbb I_F=\mathrm{GL}_1(\mathbb A_F)$ its idele group with the idele topology, $|g|_F=\prod_v|g_v|_v$ the idelic norm and $\mathbb I_F^1=\{g:\ |g|_F=1\}$ the group of norm-one ideles, with the topology induced from $\mathbb I_F$; $F^\times$ is embedded diagonally in $\mathbb I_F^1$. Let $E_0\subset\mathbb I_\infty^1$ be Tate's archimedean domain (Definition A.2.3.6, built from a $\mathbb Z$-basis of $\mathcal O_F^\times/\mu_F$, an archimedean place $v_0$ and an identification $\iota_{v_0}$ of $F_{v_0}$ with $\mathbb R$ or $\mathbb C$), let $\widehat{\mathcal O}_F^\times=\prod_{v\nmid\infty}\mathcal O_{F_v}^\times$, and let $g_1=1,g_2,\dots,g_{h_F}\in\mathbb I_F^1$ be ideles whose ideal classes $\big[\prod_{\mathfrak p}\mathfrak p^{\operatorname{ord}_{\mathfrak p}(g_{i,\mathfrak p})}\big]$ are the $h_F$ distinct elements of the ideal class group $\mathrm{Pic}(\mathcal O_F)$. Tate's idelic fundamental domain is
--   $$E_F^1=\bigcup_{i=1}^{h_F}g_i\,\big(E_0\times\widehat{\mathcal O}_F^\times\big)\subset\mathbb I_F,$$
--   where $E_0\times\widehat{\mathcal O}_F^\times$ is the set of ideles with archimedean part in $E_0$ and finite part in $\widehat{\mathcal O}_F^\times$ (`MasulloGRH.tateIdeleDomain`).
--
--   Let $\overline{E_F^1}$ be the closure of $E_F^1$ in $\mathbb I_F^1$. Then for every compact subset $K\subset\mathbb I_F^1$ there are only finitely many $\xi\in F^\times$ such that
--   $$\xi\,\overline{E_F^1}\cap K\neq\varnothing .$$
--
--   This is the local finiteness of the tiling of the norm-one ideles by the translates of Tate's fundamental domain. It is what makes sums over $F^\times$ of compactly supported functions on the ideles locally finite on $E_F^1$, and the paper uses it when unfolding integrals over the idele class group and when studying theta functions on $C_F$.
--
--   **Formalization Note.** $\mathbb I_F$ is `MasulloGRH.IdeleGroup F = (AdeleRing (𝓞 F) F)ˣ` with the units topology, $|\cdot|_F$ is the platform's `MasulloGRH.ideleNorm`, and $\mathbb I_F^1$ is the subtype `{g // ideleNorm g = 1}` with the subspace topology. The representatives are a map `r : ClassGroup (𝓞 F) → IdeleGroup F` with the hypotheses `r 1 = 1` ($g_1=1$), `ideleNorm (r c) = 1` and `ideleIdealClass F (r c) = c` (the $g_i$ have norm one and represent the classes). The statement is asserted for every basis `b`, place `v₀` and `σ ∈ Aut_ℝ(ℂ)` entering $E_0$. The closure is that of $\{g\in\mathbb I_F^1:\ g\in E_F^1\}$ in the subtype $\mathbb I_F^1$, $K$ is a compact subset of that subtype, and the condition $\xi\overline{E_F^1}\cap K\neq\varnothing$ is written as $\exists\,e\in\overline{E_F^1},\ \exists\,k\in K,\ k=\xi e$, with $\xi$ embedded by `MasulloGRH.principalIdele`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 552, Proposition A.2.3.10(3), eq. (A.2.3.27); classical reference for the domain (cited in Remark A.2.3.7, p. 549): J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, Def. 4.3.2; general references given by the paper for §A.2 (p. 545): D. Ramakrishnan, R.J. Valenza, Fourier Analysis on Number Fields, Springer, Ch. 5, §5.1; J.W.S. Cassels, A. Fröhlich, Algebraic Number Theory, London Mathematical Society, 2010, Ch. XV, §4.1, §4.3

import Mathlib
import Definitions.Def_MasulloGRH_TateIdeleDomain

open NumberField IsDedekindDomain

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace MasulloGRH

theorem tateIdeleDomain_finite_translates
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (r : ClassGroup (𝓞 F) → IdeleGroup F)
    (hr₁ : r 1 = 1) (hrn : ∀ c : ClassGroup (𝓞 F), ideleNorm (r c) = 1)
    (hr : ∀ c : ClassGroup (𝓞 F), ideleIdealClass F (r c) = c)
    (K : Set {g : IdeleGroup F // ideleNorm g = 1}) (hK : IsCompact K) :
    {ξ : Fˣ | ∃ e ∈ closure
        {g : {g : IdeleGroup F // ideleNorm g = 1} | g.val ∈ tateIdeleDomain F b v₀ σ r},
      ∃ k ∈ K, (k : IdeleGroup F) = principalIdele F ξ * (e : IdeleGroup F)}.Finite := by sorry

end MasulloGRH
