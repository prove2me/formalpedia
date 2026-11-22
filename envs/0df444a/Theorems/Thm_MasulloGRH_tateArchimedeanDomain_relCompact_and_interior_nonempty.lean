-- Prove2me | Theorems.Thm_MasulloGRH_tateArchimedeanDomain_relCompact_and_interior_nonempty
-- name    : MasulloGRH.tateArchimedeanDomain_relCompact_and_interior_nonempty
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:15.894196+00:00
-- url     : https://prove2.me/theorems/09eaa193-b898-4fee-b3f7-8c4cb231bf51
-- title:
--   Lemma A.2.3.8(1) — Tate's archimedean domain $E_0$ is relatively compact with non-empty interior in the norm-one archimedean ideles
-- statement:
--   **Tate's archimedean domain $E_0$ is relatively compact with non-empty interior** (Lemma A.2.3.8(1) of the source).
--
--   Let $F$ be a number field with $r_1$ real and $r_2$ complex places, $S_\infty$ its set of archimedean places, $\mu_F\subset\mathcal O_F^\times$ the group of roots of unity of $F$ and $w_F=|\mu_F|$. Write
--   $$\mathbb I_\infty=\mathrm{GL}_1(\mathbb A_{F,S_\infty})=\prod_{v\in S_\infty}F_v^\times,\qquad |g|_\infty=\prod_{v\in S_\infty}|g_v|_v,\qquad \mathbb I_\infty^1=\{g\in\mathbb I_\infty:\ |g|_\infty=1\},$$
--   where $|\cdot|_v$ is the normalized absolute value (the usual absolute value at a real place, its square at a complex place), and let $\mathscr L\colon\mathbb I_\infty\to\mathbb R^{S_\infty}$, $\mathscr L(g)=(\log|g_v|_v)_{v\in S_\infty}$, be the logarithm map. Fix units $\varepsilon_1,\dots,\varepsilon_r$ ($r=r_1+r_2-1$) whose classes form a $\mathbb Z$-basis of $\mathcal O_F^\times/\mu_F$, an archimedean place $v_0$, and an identification $\iota_{v_0}$ of $F_{v_0}$ with $\mathbb R$ or $\mathbb C$. Let
--   $$P=\Big\{\sum_{i=1}^{r}x_i\,\mathscr L(\varepsilon_i):\ 0\le x_i<1\Big\},\qquad E_0=\{g\in\mathscr L^{-1}(P):\ \arg(\iota_{v_0}(g_{v_0}))\in[0,2\pi/w_F)\}\subset\mathbb I_\infty^1$$
--   be the regulator parallelotope and Tate's archimedean domain (Definition A.2.3.6 of the source; `MasulloGRH.tateArchimedeanDomain`). The group $\mathcal O_F^\times$ is embedded diagonally in $\mathbb I_\infty^1$, and $\mathbb I_\infty^1$ carries the topology induced from $\mathbb I_\infty$.
--
--   Then:
--
--   1. the closure of $E_0$ in $\mathbb I_\infty^1$ is compact;
--   2. the closure of $E_0$ in $\mathbb I_\infty=\prod_{v\in S_\infty}F_v^\times$ is compact;
--   3. the interior of $E_0$ in $\mathbb I_\infty^1$ is non-empty.
--
--   Together with the tiling property (Lemma A.2.3.8(2)) this says that $E_0$ is a relatively compact fundamental domain, with non-empty interior, for the discrete cocompact subgroup $\mathcal O_F^\times$ of $\mathbb I_\infty^1$. It is the archimedean input for the corresponding properties of Tate's idelic domain $E_F^1$ (Proposition A.2.3.10) and for the finiteness of its Haar measure. The source remarks that the result "is very classical" but that it gives a proof "due to lack of a reference for a proof in standard books".
--
--   **Formalization Note.** $\mathbb I_\infty$ is `(InfiniteAdeleRing F)ˣ` and $\mathbb I_\infty^1$ is the kernel of the platform homomorphism `RiemannMasullo.infiniteIdeleNorm`, a subgroup with the subspace topology. The statement is asserted for every basis `b` of `Additive ((𝓞 F)ˣ ⧸ Units.torsion F)`, every place `v₀` and both `σ ∈ Aut_ℝ(ℂ)` (the choice of $\iota_{v_0}=\sigma\circ{}$`extensionEmbedding v₀`). The diagonal embedding is `MasulloGRH.unitsToInfiniteIdeles`. The interior in 3 is taken in the subgroup $\mathbb I_\infty^1$ (in $\mathbb I_\infty$ the interior of $E_0$ is empty); the closures in 1 and 2 are taken in $\mathbb I_\infty^1$ and in $\mathbb I_\infty$ respectively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 550, Lemma A.2.3.8(1)

import Mathlib
import Definitions.Def_MasulloGRH_TateArchimedeanDomain

open NumberField

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace MasulloGRH

theorem tateArchimedeanDomain_relCompact_and_interior_nonempty
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ) :
    IsCompact (closure (tateArchimedeanDomain F b v₀ σ)) ∧
    IsCompact (closure
      (Subtype.val '' tateArchimedeanDomain F b v₀ σ : Set (InfiniteAdeleRing F)ˣ)) ∧
    (interior (tateArchimedeanDomain F b v₀ σ)).Nonempty := by sorry

end MasulloGRH
