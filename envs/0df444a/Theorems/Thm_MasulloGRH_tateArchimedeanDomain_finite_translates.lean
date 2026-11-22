-- Prove2me | Theorems.Thm_MasulloGRH_tateArchimedeanDomain_finite_translates
-- name    : MasulloGRH.tateArchimedeanDomain_finite_translates
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:56.026072+00:00
-- url     : https://prove2.me/theorems/30d4f61a-cdae-4ab2-9d18-b530eab5482c
-- title:
--   Lemma A.2.3.8(3) — only finitely many unit translates of $\overline{E_0}$ meet a compact subset of the norm-one archimedean ideles
-- statement:
--   **Local finiteness of the unit translates of $\overline{E_0}$** (Lemma A.2.3.8(3) of the source).
--
--   Let $F$ be a number field with $r_1$ real and $r_2$ complex places, $S_\infty$ its set of archimedean places, $\mu_F\subset\mathcal O_F^\times$ the group of roots of unity of $F$ and $w_F=|\mu_F|$. Write
--   $$\mathbb I_\infty=\mathrm{GL}_1(\mathbb A_{F,S_\infty})=\prod_{v\in S_\infty}F_v^\times,\qquad |g|_\infty=\prod_{v\in S_\infty}|g_v|_v,\qquad \mathbb I_\infty^1=\{g\in\mathbb I_\infty:\ |g|_\infty=1\},$$
--   where $|\cdot|_v$ is the normalized absolute value (the usual absolute value at a real place, its square at a complex place), and let $\mathscr L\colon\mathbb I_\infty\to\mathbb R^{S_\infty}$, $\mathscr L(g)=(\log|g_v|_v)_{v\in S_\infty}$, be the logarithm map. Fix units $\varepsilon_1,\dots,\varepsilon_r$ ($r=r_1+r_2-1$) whose classes form a $\mathbb Z$-basis of $\mathcal O_F^\times/\mu_F$, an archimedean place $v_0$, and an identification $\iota_{v_0}$ of $F_{v_0}$ with $\mathbb R$ or $\mathbb C$. Let
--   $$P=\Big\{\sum_{i=1}^{r}x_i\,\mathscr L(\varepsilon_i):\ 0\le x_i<1\Big\},\qquad E_0=\{g\in\mathscr L^{-1}(P):\ \arg(\iota_{v_0}(g_{v_0}))\in[0,2\pi/w_F)\}\subset\mathbb I_\infty^1$$
--   be the regulator parallelotope and Tate's archimedean domain (Definition A.2.3.6 of the source; `MasulloGRH.tateArchimedeanDomain`). The group $\mathcal O_F^\times$ is embedded diagonally in $\mathbb I_\infty^1$, and $\mathbb I_\infty^1$ carries the topology induced from $\mathbb I_\infty$.
--
--   Let $\overline{E_0}$ be the closure of $E_0$ in $\mathbb I_\infty^1$. Then for every compact subset $K\subset\mathbb I_\infty^1$ there are only finitely many units $\xi\in\mathcal O_F^\times$ such that
--   $$\xi\,\overline{E_0}\cap K\neq\varnothing .$$
--
--   This is the local finiteness of the tiling of $\mathbb I_\infty^1$ by the translates of the fundamental domain; it is used to reduce the corresponding statement for Tate's idelic domain $E_F^1$ (Proposition A.2.3.10(3)) to the archimedean places, and to interchange sums over $\mathcal O_F^\times$ with integrals over compact sets.
--
--   **Deviation from the source.** The printed display (A.2.3.18) reads $\xi\overline{E}_0\cap\overline{E}_0\neq\varnothing$ although the sentence quantifies over a compact set $K$; the statement with $K$ is the intended one (it is the form of the parallel statements A.2.3.10(3) and A.2.4.4(3), it contains the printed case $K=\overline{E_0}$, and the proof reduces to that case).
--
--   **Formalization Note.** $\mathbb I_\infty$ is `(InfiniteAdeleRing F)ˣ` and $\mathbb I_\infty^1$ is the kernel of the platform homomorphism `RiemannMasullo.infiniteIdeleNorm`, a subgroup with the subspace topology. The statement is asserted for every basis `b` of `Additive ((𝓞 F)ˣ ⧸ Units.torsion F)`, every place `v₀` and both `σ ∈ Aut_ℝ(ℂ)` (the choice of $\iota_{v_0}=\sigma\circ{}$`extensionEmbedding v₀`). The diagonal embedding is `MasulloGRH.unitsToInfiniteIdeles`. The closure is taken in $\mathbb I_\infty^1$, and $K$ is a compact subset of $\mathbb I_\infty^1$; the condition $\xi\overline{E_0}\cap K\ne\varnothing$ is written as $\exists\,e\in\overline{E_0},\ \exists\,k\in K,\ k=\xi e$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 550, Lemma A.2.3.8(3), eq. (A.2.3.18)

import Mathlib
import Definitions.Def_MasulloGRH_TateArchimedeanDomain

open NumberField

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace MasulloGRH

theorem tateArchimedeanDomain_finite_translates
    (F : Type*) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (K : Set (MonoidHom.ker (RiemannMasullo.infiniteIdeleNorm F))) (hK : IsCompact K) :
    {u : (𝓞 F)ˣ | ∃ e ∈ closure (tateArchimedeanDomain F b v₀ σ), ∃ k ∈ K,
      (k : (InfiniteAdeleRing F)ˣ) =
        unitsToInfiniteIdeles F u * (e : (InfiniteAdeleRing F)ˣ)}.Finite := by sorry

end MasulloGRH
