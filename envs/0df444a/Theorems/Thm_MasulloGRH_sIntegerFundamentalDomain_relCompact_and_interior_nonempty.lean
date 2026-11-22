-- Prove2me | Theorems.Thm_MasulloGRH_sIntegerFundamentalDomain_relCompact_and_interior_nonempty
-- name    : MasulloGRH.sIntegerFundamentalDomain_relCompact_and_interior_nonempty
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:24.926273+00:00
-- url     : https://prove2.me/theorems/0ea61f93-1a26-4368-bae6-79ece3af9528
-- title:
--   §A.2.4.1 — the $S$-adelic fundamental domain $D_{F,S}$ is relatively compact with non-empty interior in the $S$-adeles
-- statement:
--   **The $S$-adelic fundamental domain $D_{F,S}$ is relatively compact with non-empty interior** (§A.2.4.1 of the source: the topological part of "$D_{F,S}$ is a fundamental domain").
--
--   Let $F$ be a number field of degree $d=[F:\mathbb Q]$, $S$ a finite set of places of $F$ containing all archimedean places, $S_f$ the set of finite places in $S$, $\mathbb A_{F,S}=\prod_{v\in S}F_v=\mathbb A_{F,S_\infty}\times\prod_{v\in S_f}F_v$ the ring of $S$-adeles with the product topology, and
--   $$\mathcal O_{F,S}=\{\xi\in F:\ \xi\in\mathcal O_{F_v}\ \text{for every place }v\notin S\}$$
--   the ring of $S$-integers, embedded diagonally in $\mathbb A_{F,S}$. Fix a $\mathbb Z$-basis $a_1,\dots,a_d$ of $\mathcal O_F$ and let
--   $$D_{F,\infty}=\Big\{\sum_{i=1}^{d}x_ia_i:\ 0\le x_i<1\Big\}\subset\mathbb A_{F,S_\infty}=F\otimes_{\mathbb Q}\mathbb R,\qquad D_{F,S}=D_{F,\infty}\times\prod_{v\in S_f}\mathcal O_{F_v}\subset\mathbb A_{F,S}$$
--   be the half-open parallelepiped of the integral basis and the $S$-adelic fundamental domain (Definition A.2.4.1 of the source; `MasulloGRH.sIntegerFundamentalDomain`).
--
--   Then the closure of $D_{F,S}$ in $\mathbb A_{F,S}$ is compact, and the interior of $D_{F,S}$ in $\mathbb A_{F,S}$ is non-empty.
--
--   In the source a fundamental domain for a translation action is by definition a relatively compact subset with non-empty interior whose translates tile the space (head of §A.2.1), and §A.2.4 introduces $D_{F,S}$ as such a domain for $\mathcal O_{F,S}$ acting on $\mathbb A_{F,S}$; the covering by translates and their local finiteness are Lemma A.2.4.2 (the disjointness of the translates is not part of the numbered lemma). The two properties stated here give $D_{F,S}$ finite positive Haar measure; together with the covering $\mathbb A_{F,S}=\mathcal O_{F,S}+D_{F,S}$ (Lemma A.2.4.2(1)) they show again that $\mathcal O_{F,S}$ is cocompact in $\mathbb A_{F,S}$, so that the normalization of the Tamagawa measure $\nu_S$ on $\mathbb A_{F,S}$ by total mass $1$ of the quotient $\mathbb A_{F,S}/\mathcal O_{F,S}$ (Definition A.3.1.1) makes sense.
--
--   **Deviation from the source.** Definition A.2.4.1 refers to the formula (A.2.1.1) for $D_{F,\infty}$, which as printed sums over only $r_1+r_2$ basis vectors and bounds absolute values; that set is not a fundamental domain (for $F=\mathbb Q$ it is $(-1,1)$). The half-open parallelepiped $\{\sum_{i\le d}x_ia_i:0\le x_i<1\}$ of the whole integral basis is used instead; it is the set the source itself uses in the proof of Lemma A.2.4.2 ("$D_{F,\infty}$ is sent homeomorphically onto $[0,1)^{[F:\mathbb Q]}$") and in Example A.2.1.3. The numbered Lemma A.2.4.2 lists only the covering and the local finiteness; relative compactness and non-emptiness of the interior are further parts of the notion of fundamental domain used in §A.2.4 and are stated here separately.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places (prime ideals of $\mathcal O_F$); $\mathbb A_{F,S}$, the diagonal embedding and $\mathcal O_{F,S}$ are the platform's `MasulloGRH.SAdeleRing F Sf`, `MasulloGRH.sDiagonal Sf` and `MasulloGRH.SIntegers Sf` (Mathlib's `Set.integer`), and the integral basis is `b : Module.Basis ι ℤ (𝓞 F)`. For `Sf = ∅` the statement is about the lattice $\mathcal O_F\subset F\otimes_{\mathbb Q}\mathbb R$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 553–554, §A.2.4 and Definition A.2.4.1 (notion of fundamental domain: head of §A.2.1, p. 545)

import Mathlib
import Definitions.Def_MasulloGRH_SIntegerFundamentalDomain

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sIntegerFundamentalDomain_relCompact_and_interior_nonempty
    (F : Type*) [Field F] [NumberField F] {ι : Type*} (b : Module.Basis ι ℤ (𝓞 F))
    (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (closure (sIntegerFundamentalDomain F b Sf)) ∧
    (interior (sIntegerFundamentalDomain F b Sf)).Nonempty := by sorry

end MasulloGRH
