-- Prove2me | Theorems.Thm_NumberField_SClassGroup_pic_localization_exact
-- name    : NumberField.SClassGroup.pic_localization_exact
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:31.196403+00:00
-- url     : https://prove2.me/theorems/eef591a5-ae21-484c-bb65-2434c265a2ae
-- title:
--   Eq. (A.1.5.9) — localization exact sequence $\mathcal O_{F,T}^\times\to\mathbb Z^{T\setminus S}\to\mathrm{Pic}(\mathcal O_{F,S})\to\mathrm{Pic}(\mathcal O_{F,T})\to 1$ for $S$-class groups
-- statement:
--   **Localization exact sequence for the class groups of rings of $S$-integers** (eq. (A.1.5.9) of the source).
--
--   Let $F$ be a number field with ring of integers $\mathcal O_F$, and let $S\subseteq T$ be finite sets of nonzero prime ideals of $\mathcal O_F$. For a set $X$ of primes write
--   $$\mathcal O_{F,X}=\{x\in F:\ \operatorname{ord}_{\mathfrak p}(x)\ge 0\ \text{for all }\mathfrak p\notin X\},\qquad \mathcal O_{F,X}^\times=\{x\in F^\times:\ \operatorname{ord}_{\mathfrak p}(x)=0\ \text{for all }\mathfrak p\notin X\}$$
--   for the ring of $X$-integers and the group of $X$-units, so that $\mathcal O_F\subseteq\mathcal O_{F,S}\subseteq\mathcal O_{F,T}$. Let
--   $$p\colon\operatorname{Pic}(\mathcal O_{F,S})\longrightarrow\operatorname{Pic}(\mathcal O_{F,T})$$
--   be the base-change homomorphism of Picard groups (ideal class groups) along the inclusion $\mathcal O_{F,S}\subseteq\mathcal O_{F,T}$, and for $n=(n_{\mathfrak p})\in\mathbb Z^{T\setminus S}$ put
--   $$c(n)=\prod_{\mathfrak p\in T\setminus S}[\mathfrak p\,\mathcal O_{F,S}]^{\,n_{\mathfrak p}}\in\operatorname{Pic}(\mathcal O_{F,S}),$$
--   where $[\mathfrak p\,\mathcal O_{F,S}]$ is the image of the class of $\mathfrak p$ under base change $\operatorname{Pic}(\mathcal O_F)\to\operatorname{Pic}(\mathcal O_{F,S})$. Then:
--
--   1. $p$ is surjective.
--   2. $\ker p=\{c(n):\ n\in\mathbb Z^{T\setminus S}\}$: a class of $\mathcal O_{F,S}$ becomes trivial in $\mathcal O_{F,T}$ exactly when it is a product of powers of the classes of the primes in $T\setminus S$.
--   3. $c(n)=1$ if and only if there is a $T$-unit $u\in\mathcal O_{F,T}^\times$ with $\operatorname{ord}_{\mathfrak p}(u)=n_{\mathfrak p}$ for every $\mathfrak p\in T\setminus S$.
--
--   In other words, the sequence
--   $$\mathcal O_{F,T}^\times\xrightarrow{\ (\operatorname{ord}_{\mathfrak p})_{\mathfrak p\in T\setminus S}\ }\mathbb Z^{T\setminus S}\xrightarrow{\ c\ }\operatorname{Pic}(\mathcal O_{F,S})\xrightarrow{\ p\ }\operatorname{Pic}(\mathcal O_{F,T})\longrightarrow 1$$
--   is exact. After identifying $F_v^\times/\mathcal O_{F_v}^\times\cong\mathbb Z$ through the normalized valuation, this is the exact sequence
--   $$1\to\Big(\prod_{v\in S'_f-S_f}F_v^\times/\mathcal O_{F_v}^\times\Big)\Big/\mathcal O_{F,S'}^\times\to\operatorname{Pic}(\mathcal O_{F,S})\to\operatorname{Pic}(\mathcal O_{F,S'})\to 0$$
--   of the source, in which $S\subseteq S'$ are finite sets of places containing the Archimedean places and $S_f$, $S'_f$ (here $S$, $T$) are their sets of finite places.
--
--   This is the classical comparison between the class groups of two rings of $S$-integers in terms of $S$-units. The paper uses it, after enlarging $S'$ until $\operatorname{Pic}(\mathcal O_{F,S'})=1$, to present $\operatorname{Pic}(\mathcal O_{F,S})$ and $\operatorname{Pic}(\mathcal O_F)$ as quotients of $\prod_v F_v^\times/\mathcal O_{F_v}^\times$ by $S'$-units (Remark A.1.5.3 and eq. (A.1.5.10)).
--
--   **Formalization Note.** $\mathcal O_{F,X}$ and $\mathcal O_{F,X}^\times$ are Mathlib's `Set.integer` and `Set.unit`; $\operatorname{Pic}$ is `CommRing.Pic`, $p$ is `CommRing.Pic.mapRingHom` of the inclusion, and $[\mathfrak p\,\mathcal O_{F,S}]$ is `CommRing.Pic.mapAlgebra (𝓞 F) 𝒪_{F,S}` applied to the image of the ideal class of $\mathfrak p$ under `ClassGroup.equivPic`. Mathlib's valuation is $v_{\mathfrak p}(x)=\exp(-\operatorname{ord}_{\mathfrak p}(x))$, so $\operatorname{ord}_{\mathfrak p}(u)=n_{\mathfrak p}$ is written `valuation u = WithZero.exp (-n)`. The group $\prod_v F_v^\times/\mathcal O_{F_v}^\times$ of the source is replaced by $\mathbb Z^{T\setminus S}$; the Archimedean places play no role and do not appear. The `DecidableEq` hypothesis is only needed to form the finite set $T\setminus S$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 544, §A.1.5.3, eq. (A.1.5.9)

import Mathlib

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace NumberField.SClassGroup

theorem pic_localization_exact (F : Type*) [Field F] [NumberField F]
    [DecidableEq (HeightOneSpectrum (𝓞 F))]
    (S T : Finset (HeightOneSpectrum (𝓞 F))) (h : S ⊆ T) :
    let A := (S : Set (HeightOneSpectrum (𝓞 F))).integer F
    let B := (T : Set (HeightOneSpectrum (𝓞 F))).integer F
    let i : A →+* B := (Subalgebra.inclusion (S := A) (T := B)
      (fun _ hx v hv => hx v (fun hvS => hv (h hvS)))).toRingHom
    let p : CommRing.Pic A →* CommRing.Pic B := CommRing.Pic.mapRingHom i
    let c : (↥(T \ S) → ℤ) → CommRing.Pic A := fun n =>
      CommRing.Pic.mapAlgebra (𝓞 F) A (∏ v : ↥(T \ S),
        (ClassGroup.equivPic (𝓞 F) (ClassGroup.mk0
          ⟨v.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.1.ne_bot⟩)) ^ n v)
    Function.Surjective p ∧
    (∀ x : CommRing.Pic A, p x = 1 ↔ ∃ n : ↥(T \ S) → ℤ, c n = x) ∧
    (∀ n : ↥(T \ S) → ℤ, c n = 1 ↔
      ∃ u : Fˣ, u ∈ (T : Set (HeightOneSpectrum (𝓞 F))).unit F ∧
        ∀ v : ↥(T \ S), v.1.valuation F (u : F) = WithZero.exp (-(n v))) := by sorry

end NumberField.SClassGroup
