-- Prove2me | Theorems.Thm_MasulloGRH_tateArchimedeanDomain_existsUnique_unit_mul
-- name    : MasulloGRH.tateArchimedeanDomain_existsUnique_unit_mul
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:27.163441+00:00
-- url     : https://prove2.me/theorems/f70c9ded-11de-49cb-9487-54bcd6d19320
-- title:
--   Lemma A.2.3.8(2) — every norm-one archimedean idele is $u\,e$ for a unique unit $u\in\mathcal O_F^\times$ and $e\in E_0$
-- statement:
--   **Tate's archimedean domain $E_0$ is a strict fundamental domain for the units** (Lemma A.2.3.8(2), eq. (A.2.3.17) of the source).
--
--   Let $F$ be a number field with $r_1$ real and $r_2$ complex places, $S_\infty$ its set of archimedean places, $\mu_F\subset\mathcal O_F^\times$ the group of roots of unity of $F$ and $w_F=|\mu_F|$. Write
--   $$\mathbb I_\infty=\mathrm{GL}_1(\mathbb A_{F,S_\infty})=\prod_{v\in S_\infty}F_v^\times,\qquad |g|_\infty=\prod_{v\in S_\infty}|g_v|_v,\qquad \mathbb I_\infty^1=\{g\in\mathbb I_\infty:\ |g|_\infty=1\},$$
--   where $|\cdot|_v$ is the normalized absolute value (the usual absolute value at a real place, its square at a complex place), and let $\mathscr L\colon\mathbb I_\infty\to\mathbb R^{S_\infty}$, $\mathscr L(g)=(\log|g_v|_v)_{v\in S_\infty}$, be the logarithm map. Fix units $\varepsilon_1,\dots,\varepsilon_r$ ($r=r_1+r_2-1$) whose classes form a $\mathbb Z$-basis of $\mathcal O_F^\times/\mu_F$, an archimedean place $v_0$, and an identification $\iota_{v_0}$ of $F_{v_0}$ with $\mathbb R$ or $\mathbb C$. Let
--   $$P=\Big\{\sum_{i=1}^{r}x_i\,\mathscr L(\varepsilon_i):\ 0\le x_i<1\Big\},\qquad E_0=\{g\in\mathscr L^{-1}(P):\ \arg(\iota_{v_0}(g_{v_0}))\in[0,2\pi/w_F)\}\subset\mathbb I_\infty^1$$
--   be the regulator parallelotope and Tate's archimedean domain (Definition A.2.3.6 of the source; `MasulloGRH.tateArchimedeanDomain`). The group $\mathcal O_F^\times$ is embedded diagonally in $\mathbb I_\infty^1$, and $\mathbb I_\infty^1$ carries the topology induced from $\mathbb I_\infty$.
--
--   Then for every $g\in\mathbb I_\infty^1$ there is exactly one unit $u\in\mathcal O_F^\times$ such that
--   $$g=u\,e\qquad\text{for some }e\in E_0 .$$
--   Equivalently,
--   $$\mathcal O_F^\times E_0=\mathbb I_\infty^1\qquad\text{and}\qquad \xi E_0\cap E_0=\varnothing\quad\text{for every }\xi\in\mathcal O_F^\times,\ \xi\ne1 .$$
--
--   This is the sharp form of Dirichlet's unit theorem as a statement about the action of the full unit group (roots of unity included) on the norm-one archimedean ideles: the parallelotope $P$ is a fundamental domain for the lattice $\mathscr L(\mathcal O_F^\times)\subset H_{\log}$, and the sector $[0,2\pi/w_F)$ at the place $v_0$ is a fundamental domain for $\mu_F$. It is the key step in Tate's construction of the fundamental domain $E_F^1$ for $F^\times$ acting on the norm-one ideles (Proposition A.2.3.10(2)).
--
--   **Formalization Note.** $\mathbb I_\infty$ is `(InfiniteAdeleRing F)ˣ` and $\mathbb I_\infty^1$ is the kernel of the platform homomorphism `RiemannMasullo.infiniteIdeleNorm`, a subgroup with the subspace topology. The statement is asserted for every basis `b` of `Additive ((𝓞 F)ˣ ⧸ Units.torsion F)`, every place `v₀` and both `σ ∈ Aut_ℝ(ℂ)` (the choice of $\iota_{v_0}=\sigma\circ{}$`extensionEmbedding v₀`). The diagonal embedding is `MasulloGRH.unitsToInfiniteIdeles`. The two assertions of the source (covering and disjointness of the translates) are stated together as `∃!`: existence of $u$ is the covering $\mathcal O_F^\times E_0=\mathbb I_\infty^1$, and uniqueness of $u$ is equivalent to $\xi E_0\cap E_0=\varnothing$ for $\xi\ne1$ (the element $e=u^{-1}g$ is determined by $u$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 550, Lemma A.2.3.8(2), eq. (A.2.3.17)

import Mathlib
import Definitions.Def_MasulloGRH_TateArchimedeanDomain

open NumberField

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace MasulloGRH

theorem tateArchimedeanDomain_existsUnique_unit_mul
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (g : MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F)) :
    ∃! u : (𝓞 F)ˣ, ∃ e ∈ tateArchimedeanDomain F b v₀ σ,
      (g : (InfiniteAdeleRing F)ˣ) =
        unitsToInfiniteIdeles F u * (e : (InfiniteAdeleRing F)ˣ) := by sorry

end MasulloGRH
