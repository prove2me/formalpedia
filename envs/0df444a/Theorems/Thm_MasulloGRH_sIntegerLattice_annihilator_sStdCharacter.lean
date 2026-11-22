-- Prove2me | Theorems.Thm_MasulloGRH_sIntegerLattice_annihilator_sStdCharacter
-- name    : MasulloGRH.sIntegerLattice_annihilator_sStdCharacter
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:51:05.014592+00:00
-- url     : https://prove2.me/theorems/c3101bd2-35ef-457d-98db-74af4f456cc9
-- title:
--   Example A.3.1.11 — $\mathcal O_{F,S}^{\perp}=\mathcal O_{F,S}$ in $\mathbb A_{F,S}$ for the pairing $\psi_{S,\mathrm{std}}(xy)$, when $S$ contains the places ramified over $\mathbb Q$
-- statement:
--   **The lattice of $S$-integers is its own annihilator** (Example A.3.1.11, "$S$-local dual lattices", of the source).
--
--   Let $F$ be a number field. Let $S$ be a finite set of places of $F$ containing all archimedean places and $S_f\subset S$ the set of its finite places. Write
--   $$\mathbb A_{F,S}=\prod_{v\in S}F_v,\qquad \mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times,\qquad |g|_{F,S}=\prod_{v\in S}|g_v|_v$$
--   for the ring of $S$-adeles (with the product topology), the group of $S$-ideles and the $S$-idelic norm, and
--   $$\mathcal O_{F,S}=\{\xi\in F:\ \xi\in\mathcal O_{F_v}\ \text{for every place }v\notin S\}$$
--   for the ring of $S$-integers, embedded diagonally in $\mathbb A_{F,S}$ as a discrete cocompact subgroup.
--
--   Let $\psi_{S,\mathrm{std}}=\bigotimes_{v\in S}\psi_v\colon\mathbb A_{F,S}\to\mathrm U(1)$ be the standard additive character (eq. (A.3.1.9); `MasulloGRH.sStdCharacter`), the product of the local standard characters $\psi_w(x)=e^{-2\pi i\,\mathrm{Tr}_{F_w/\mathbb R}(x)}$ ($w\mid\infty$) and $\psi_v(x)=e^{2\pi i\{\mathrm{Tr}_{F_v/\mathbb Q_p}(x)\}_p}$ ($v\mid p$ finite), and
--   $$\langle x,y\rangle_S=\psi_{S,\mathrm{std}}(xy)\qquad(x,y\in\mathbb A_{F,S})$$
--   the duality pairing (A.3.1.10), which identifies $\mathbb A_{F,S}$ with its Pontryagin dual.
--
--   Assume that $S$ contains every finite place of $F$ that is ramified over $\mathbb Q$. Then the annihilator of the discrete cocompact subgroup $\Gamma=\mathcal O_{F,S}\subset\mathbb A_{F,S}$ with respect to this pairing is $\mathcal O_{F,S}$ itself: for $y\in\mathbb A_{F,S}$,
--   $$\big(\forall x\in\mathcal O_{F,S}:\ \psi_{S,\mathrm{std}}(xy)=1\big)\iff y\in\mathcal O_{F,S}.$$
--
--   Thus $\Gamma^\perp=\Gamma$, and the Pontryagin dual of the compact group $\mathbb A_{F,S}/\mathcal O_{F,S}$ is $\mathcal O_{F,S}$. This is the $S$-local counterpart of the self-duality $F^\perp=F$ of the adele ring; it is the input of the $S$-local Poisson summation formula $\sum_{\xi\in\mathcal O_{F,S}}f(\xi)=\sum_{\xi\in\mathcal O_{F,S}}\hat f(\xi)$ underlying the $S$-local $\theta$-functions. The ramification hypothesis is needed: in general the annihilator is $\mathfrak d_{F/\mathbb Q}^{-1}\mathcal O_{F,S}$ (for $F=\mathbb Q(i)$ and $S=S_\infty$ it is $\tfrac12\mathbb Z[i]$).
--
--   **Deviation from the source.** With the local characters as printed in Examples A.3.1.5–A.3.1.8 (the same sign at the real and the $p$-adic places) the statement is false: for $F=\mathbb Q$, $S=\{\infty,3\}$ the pairing of $1/3$ and $1$ is $e^{4\pi i/3}$. The statement is formalized for the character with the sign convention of Tate's thesis, as in `MasulloGRH.sStdCharacter`.
--
--   **Formalization Note.** $S$ is represented by the finite set `Sf` of its finite places, and "$S$ contains the ramified places" is: every prime of $\mathcal O_F$ dividing the different `differentIdeal ℤ (𝓞 F)` belongs to `Sf`. $\mathcal O_{F,S}\subset\mathbb A_{F,S}$ is the additive subgroup `MasulloGRH.sIntegerLattice Sf`, the image of the diagonal embedding.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 558–559, Example A.3.1.11 ($S$-local dual lattices), eqs. (A.3.1.9)–(A.3.1.13)

import Mathlib
import Definitions.Def_MasulloGRH_SLocalStandardCharacter

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace MasulloGRH

theorem sIntegerLattice_annihilator_sStdCharacter
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ Sf)
    (y : SAdeleRing F Sf) :
    (∀ x ∈ sIntegerLattice Sf, sStdCharacter Sf (x * y) = 1) ↔ y ∈ sIntegerLattice Sf := by sorry

end MasulloGRH
