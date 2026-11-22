-- Prove2me | Theorems.Thm_MasulloGRH_sIntegerFundamentalDomain_existsUnique
-- name    : MasulloGRH.sIntegerFundamentalDomain_existsUnique
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:53.613336+00:00
-- url     : https://prove2.me/theorems/0cb34042-4c53-4065-811a-c6f269ee336c
-- title:
--   Lemma A.2.4.2(1) — every $S$-adele is $\xi+y$ for a unique $S$-integer $\xi\in\mathcal O_{F,S}$ and $y\in D_{F,S}$
-- statement:
--   **$D_{F,S}$ is a strict fundamental domain for the $S$-integers acting on the $S$-adeles** (Lemma A.2.4.2(1), eq. (A.2.4.2) of the source, together with the disjointness of the translates).
--
--   Let $F$ be a number field of degree $d=[F:\mathbb Q]$, $S$ a finite set of places of $F$ containing all archimedean places, $S_f$ the set of finite places in $S$, $\mathbb A_{F,S}=\prod_{v\in S}F_v=\mathbb A_{F,S_\infty}\times\prod_{v\in S_f}F_v$ the ring of $S$-adeles with the product topology, and
--   $$\mathcal O_{F,S}=\{\xi\in F:\ \xi\in\mathcal O_{F_v}\ \text{for every place }v\notin S\}$$
--   the ring of $S$-integers, embedded diagonally in $\mathbb A_{F,S}$. Fix a $\mathbb Z$-basis $a_1,\dots,a_d$ of $\mathcal O_F$ and let
--   $$D_{F,\infty}=\Big\{\sum_{i=1}^{d}x_ia_i:\ 0\le x_i<1\Big\}\subset\mathbb A_{F,S_\infty}=F\otimes_{\mathbb Q}\mathbb R,\qquad D_{F,S}=D_{F,\infty}\times\prod_{v\in S_f}\mathcal O_{F_v}\subset\mathbb A_{F,S}$$
--   be the half-open parallelepiped of the integral basis and the $S$-adelic fundamental domain (Definition A.2.4.1 of the source; `MasulloGRH.sIntegerFundamentalDomain`).
--
--   Then for every $x\in\mathbb A_{F,S}$ there is exactly one $S$-integer $\xi\in\mathcal O_{F,S}$ such that
--   $$x-\xi\in D_{F,S}.$$
--   Equivalently,
--   $$\mathbb A_{F,S}=\mathcal O_{F,S}+D_{F,S}\qquad\text{and}\qquad(\xi+D_{F,S})\cap D_{F,S}=\varnothing\quad\text{for every }\xi\in\mathcal O_{F,S},\ \xi\neq0 .$$
--
--   This is the $S$-adelic version of the classical statement $\mathbb A_F=F+D_F$ with $D_F=D_{F,\infty}\times\widehat{\mathcal O}_F$ (Lemma A.2.1.2): the covering follows from strong approximation (every element of $\prod_{v\in S_f}F_v$ is congruent to an $S$-integer modulo $\prod_{v\in S_f}\mathcal O_{F_v}$) together with the fact that $D_{F,\infty}$ is a fundamental parallelepiped for the lattice $\mathcal O_F$ in $F\otimes_{\mathbb Q}\mathbb R$. It identifies $\mathbb A_{F,S}/\mathcal O_{F,S}$ with $D_{F,S}$ as a set, and is used to normalize and compute with the Tamagawa measure on $\mathbb A_{F,S}$ and to unfold integrals over $\mathbb A_{F,S}/\mathcal O_{F,S}$.
--
--   **Deviation from the source.** Definition A.2.4.1 refers to the formula (A.2.1.1) for $D_{F,\infty}$, which as printed sums over only $r_1+r_2$ basis vectors and bounds absolute values; that set is not a fundamental domain (for $F=\mathbb Q$ it is $(-1,1)$). The half-open parallelepiped $\{\sum_{i\le d}x_ia_i:0\le x_i<1\}$ of the whole integral basis is used instead; it is the set the source itself uses in the proof of Lemma A.2.4.2 ("$D_{F,\infty}$ is sent homeomorphically onto $[0,1)^{[F:\mathbb Q]}$") and in Example A.2.1.3. The numbered item (1) of the lemma states only the covering $\mathbb A_{F,S}=\mathcal O_{F,S}+D_{F,S}$; the uniqueness of $\xi$ (disjointness of the non-trivial translates) is the other half of the notion of fundamental domain announced in §A.2.4 and defined at the head of §A.2.1, and is included.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places (prime ideals of $\mathcal O_F$); $\mathbb A_{F,S}$, the diagonal embedding and $\mathcal O_{F,S}$ are the platform's `MasulloGRH.SAdeleRing F Sf`, `MasulloGRH.sDiagonal Sf` and `MasulloGRH.SIntegers Sf` (Mathlib's `Set.integer`), and the integral basis is `b : Module.Basis ι ℤ (𝓞 F)`. For `Sf = ∅` the statement is about the lattice $\mathcal O_F\subset F\otimes_{\mathbb Q}\mathbb R$. The quantifier `∃! ξ : F` is restricted to $S$-integers by the conjunct `ξ ∈ SIntegers Sf` (uniqueness would fail over all of $F$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 554, Lemma A.2.4.2(1), eq. (A.2.4.2) (notion of fundamental domain: head of §A.2.1, p. 545, and §A.2.4, p. 553)

import Mathlib
import Definitions.Def_MasulloGRH_SIntegerFundamentalDomain

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sIntegerFundamentalDomain_existsUnique
    (F : Type*) [Field F] [NumberField F] {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) (x : SAdeleRing F Sf) :
    ∃! ξ : F, ξ ∈ SIntegers (F := F) Sf ∧
      x - sDiagonal Sf ξ ∈ sIntegerFundamentalDomain F b Sf := by sorry

end MasulloGRH
