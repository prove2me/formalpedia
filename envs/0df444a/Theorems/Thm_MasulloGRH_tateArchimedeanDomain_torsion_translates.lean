-- Prove2me | Theorems.Thm_MasulloGRH_tateArchimedeanDomain_torsion_translates
-- name    : MasulloGRH.tateArchimedeanDomain_torsion_translates
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:27.805853+00:00
-- url     : https://prove2.me/theorems/46180bfb-e9aa-4a46-a34a-978d366ec396
-- title:
--   Lemma A.2.3.8(2) — $\mu_FE_0=\mathscr L^{-1}(P)$: the roots of unity translate $E_0$ onto the preimage of the regulator parallelotope
-- statement:
--   **The translates of $E_0$ by the roots of unity fill the preimage of the regulator parallelotope** (last assertion of Lemma A.2.3.8(2) of the source).
--
--   Let $F$ be a number field with $r_1$ real and $r_2$ complex places, $S_\infty$ its set of archimedean places, $\mu_F\subset\mathcal O_F^\times$ the group of roots of unity of $F$ and $w_F=|\mu_F|$. Write
--   $$\mathbb I_\infty=\mathrm{GL}_1(\mathbb A_{F,S_\infty})=\prod_{v\in S_\infty}F_v^\times,\qquad |g|_\infty=\prod_{v\in S_\infty}|g_v|_v,\qquad \mathbb I_\infty^1=\{g\in\mathbb I_\infty:\ |g|_\infty=1\},$$
--   where $|\cdot|_v$ is the normalized absolute value (the usual absolute value at a real place, its square at a complex place), and let $\mathscr L\colon\mathbb I_\infty\to\mathbb R^{S_\infty}$, $\mathscr L(g)=(\log|g_v|_v)_{v\in S_\infty}$, be the logarithm map. Fix units $\varepsilon_1,\dots,\varepsilon_r$ ($r=r_1+r_2-1$) whose classes form a $\mathbb Z$-basis of $\mathcal O_F^\times/\mu_F$, an archimedean place $v_0$, and an identification $\iota_{v_0}$ of $F_{v_0}$ with $\mathbb R$ or $\mathbb C$. Let
--   $$P=\Big\{\sum_{i=1}^{r}x_i\,\mathscr L(\varepsilon_i):\ 0\le x_i<1\Big\},\qquad E_0=\{g\in\mathscr L^{-1}(P):\ \arg(\iota_{v_0}(g_{v_0}))\in[0,2\pi/w_F)\}\subset\mathbb I_\infty^1$$
--   be the regulator parallelotope and Tate's archimedean domain (Definition A.2.3.6 of the source; `MasulloGRH.tateArchimedeanDomain`). The group $\mathcal O_F^\times$ is embedded diagonally in $\mathbb I_\infty^1$, and $\mathbb I_\infty^1$ carries the topology induced from $\mathbb I_\infty$.
--
--   Then
--   $$\mu_F\,E_0=\mathscr L^{-1}(P),$$
--   that is, a norm-one archimedean idele $g\in\mathbb I_\infty^1$ satisfies $\mathscr L(g)\in P$ if and only if $g=\zeta e$ for some root of unity $\zeta\in\mu_F$ and some $e\in E_0$.
--
--   The logarithm map does not see the roots of unity, so $\mathscr L^{-1}(P)$ is only a fundamental domain for $\mathcal O_F^\times/\mu_F$; the statement says that the angular condition at $v_0$ cuts it into exactly the $\mu_F$-translates of $E_0$. It is the link between the lattice statement in logarithmic space (the parallelotope $P$ tiles $H_{\log}$ under $\mathscr L(\mathcal O_F^\times)$) and the fundamental-domain property of $E_0$ for the full unit group; together with the disjointness of the unit translates of $E_0$ it gives $\operatorname{vol}(\mathscr L^{-1}(P))=w_F\operatorname{vol}(E_0)$ for every Haar measure on $\mathbb I_\infty^1$, which is how the number $w_F$ of roots of unity enters volume computations with Tate's fundamental domain.
--
--   **Formalization Note.** $\mathbb I_\infty$ is `(InfiniteAdeleRing F)ˣ` and $\mathbb I_\infty^1$ is the kernel of the platform homomorphism `RiemannMasullo.infiniteIdeleNorm`, a subgroup with the subspace topology. The statement is asserted for every basis `b` of `Additive ((𝓞 F)ˣ ⧸ Units.torsion F)`, every place `v₀` and both `σ ∈ Aut_ℝ(ℂ)` (the choice of $\iota_{v_0}=\sigma\circ{}$`extensionEmbedding v₀`). The diagonal embedding is `MasulloGRH.unitsToInfiniteIdeles`. $\mathscr L^{-1}(P)$ is `MasulloGRH.logParallelotopePreimage F b`, a subset of $\mathbb I_\infty^1$, and $\mu_F$ is Mathlib's `Units.torsion F`. The set equality is stated elementwise.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 550, Lemma A.2.3.8(2), last sentence

import Mathlib
import Definitions.Def_MasulloGRH_TateArchimedeanDomain

open NumberField

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace MasulloGRH

theorem tateArchimedeanDomain_torsion_translates
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (g : MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F)) :
    g ∈ logParallelotopePreimage F b ↔
      ∃ ζ ∈ Units.torsion F, ∃ e ∈ tateArchimedeanDomain F b v₀ σ,
        (g : (InfiniteAdeleRing F)ˣ) =
          unitsToInfiniteIdeles F ζ * (e : (InfiniteAdeleRing F)ˣ) := by sorry

end MasulloGRH
