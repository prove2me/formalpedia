-- Prove2me | Theorems.Thm_MasulloGRH_sIntegerFundamentalDomain_finite_translates
-- name    : MasulloGRH.sIntegerFundamentalDomain_finite_translates
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:24.816804+00:00
-- url     : https://prove2.me/theorems/888f12cc-c508-4051-b1f3-460d6dabfff0
-- title:
--   Lemma A.2.4.2(2) — only finitely many $\mathcal O_{F,S}$-translates of $\overline{D_{F,S}}$ meet a compact subset of the $S$-adeles
-- statement:
--   **Local finiteness of the $\mathcal O_{F,S}$-translates of $\overline{D_{F,S}}$** (Lemma A.2.4.2(2), eq. (A.2.4.3) of the source).
--
--   Let $F$ be a number field of degree $d=[F:\mathbb Q]$, $S$ a finite set of places of $F$ containing all archimedean places, $S_f$ the set of finite places in $S$, $\mathbb A_{F,S}=\prod_{v\in S}F_v=\mathbb A_{F,S_\infty}\times\prod_{v\in S_f}F_v$ the ring of $S$-adeles with the product topology, and
--   $$\mathcal O_{F,S}=\{\xi\in F:\ \xi\in\mathcal O_{F_v}\ \text{for every place }v\notin S\}$$
--   the ring of $S$-integers, embedded diagonally in $\mathbb A_{F,S}$. Fix a $\mathbb Z$-basis $a_1,\dots,a_d$ of $\mathcal O_F$ and let
--   $$D_{F,\infty}=\Big\{\sum_{i=1}^{d}x_ia_i:\ 0\le x_i<1\Big\}\subset\mathbb A_{F,S_\infty}=F\otimes_{\mathbb Q}\mathbb R,\qquad D_{F,S}=D_{F,\infty}\times\prod_{v\in S_f}\mathcal O_{F_v}\subset\mathbb A_{F,S}$$
--   be the half-open parallelepiped of the integral basis and the $S$-adelic fundamental domain (Definition A.2.4.1 of the source; `MasulloGRH.sIntegerFundamentalDomain`).
--
--   Let $\overline{D_{F,S}}$ be the closure of $D_{F,S}$ in $\mathbb A_{F,S}$. Then for every compact subset $K\subset\mathbb A_{F,S}$ there are only finitely many $S$-integers $\xi\in\mathcal O_{F,S}$ such that
--   $$(\xi+\overline{D_{F,S}})\cap K\neq\varnothing .$$
--
--   This is the local finiteness of the tiling of the $S$-adeles by the translates of the fundamental domain; it reflects the discreteness of $\mathcal O_{F,S}$ in $\mathbb A_{F,S}$ and is used to control sums over $\mathcal O_{F,S}$ of compactly supported (Schwartz–Bruhat) functions on $\mathbb A_{F,S}$, e.g. in $S$-local Poisson summation and theta functions.
--
--   **Deviation from the source.** Definition A.2.4.1 refers to the formula (A.2.1.1) for $D_{F,\infty}$, which as printed sums over only $r_1+r_2$ basis vectors and bounds absolute values; that set is not a fundamental domain (for $F=\mathbb Q$ it is $(-1,1)$). The half-open parallelepiped $\{\sum_{i\le d}x_ia_i:0\le x_i<1\}$ of the whole integral basis is used instead; it is the set the source itself uses in the proof of Lemma A.2.4.2 ("$D_{F,\infty}$ is sent homeomorphically onto $[0,1)^{[F:\mathbb Q]}$") and in Example A.2.1.3.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places (prime ideals of $\mathcal O_F$); $\mathbb A_{F,S}$, the diagonal embedding and $\mathcal O_{F,S}$ are the platform's `MasulloGRH.SAdeleRing F Sf`, `MasulloGRH.sDiagonal Sf` and `MasulloGRH.SIntegers Sf` (Mathlib's `Set.integer`), and the integral basis is `b : Module.Basis ι ℤ (𝓞 F)`. For `Sf = ∅` the statement is about the lattice $\mathcal O_F\subset F\otimes_{\mathbb Q}\mathbb R$. The condition $(\xi+\overline{D_{F,S}})\cap K\ne\varnothing$ is written as $\exists\,y\in\overline{D_{F,S}},\ \xi+y\in K$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 554, Lemma A.2.4.2(2), eq. (A.2.4.3)

import Mathlib
import Definitions.Def_MasulloGRH_SIntegerFundamentalDomain

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sIntegerFundamentalDomain_finite_translates
    (F : Type*) [Field F] [NumberField F] {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
    (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (K : Set (SAdeleRing F Sf)) (hK : IsCompact K) :
    {ξ : F | ξ ∈ SIntegers (F := F) Sf ∧
      ∃ y ∈ closure (sIntegerFundamentalDomain F b Sf), sDiagonal Sf ξ + y ∈ K}.Finite := by sorry

end MasulloGRH
