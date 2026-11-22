-- Prove2me | Theorems.Thm_MasulloGRH_infiniteLocalMulTamagawa_isHaarMeasure
-- name    : MasulloGRH.infiniteLocalMulTamagawa_isHaarMeasure
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:47.062339+00:00
-- url     : https://prove2.me/theorems/95afbdd0-ce27-4918-9b69-b57d9cab12c3
-- title:
--   Definition A.3.2.2(1) — $\mu_w=|\cdot|_w^{-1}\,\nu_w$ is a Haar measure on $F_w^\times$ at an archimedean place $w$
-- statement:
--   **The archimedean local multiplicative Tamagawa measure is a Haar measure** (Definition A.3.2.2(1) of the source).
--
--   Let $F$ be a number field and $w$ an archimedean place of $F$, with completion $F_w\simeq\mathbb R$ or $\mathbb C$. Let $|\cdot|_w$ be the normalized absolute value on $F_w$ (the usual absolute value if $F_w\simeq\mathbb R$, its square if $F_w\simeq\mathbb C$) and $\nu_w$ the local additive Tamagawa measure on $F_w$ (Definition A.3.1.2): Lebesgue measure $dx$ if $F_w\simeq\mathbb R$, and $|dz\wedge d\bar z|=2\,dx\,dy$ if $F_w\simeq\mathbb C$.
--
--   The **local multiplicative Tamagawa measure** on $F_w^\times$ is $\mu_w=|\cdot|_w^{-1}\,\nu_w|_{F_w^\times}$, i.e.
--   $$\mu_w(B)=\int_B\frac{d\nu_w(x)}{|x|_w}\qquad(B\subset F_w^\times\ \text{Borel})$$
--   (`MasulloGRH.infiniteLocalMulTamagawa`): the measure $dx/|x|$ on $\mathbb R^\times$ and $2\,dx\,dy/|z|^2$ on $\mathbb C^\times$. Then $\mu_w$ is a Haar measure on the multiplicative group $F_w^\times$: it is invariant under multiplication, finite on compact subsets of $F_w^\times$ and positive on non-empty open subsets.
--
--   This is the assertion "a Haar measure since $|\cdot|_w$ is normalized" of the source: multiplication by $a\in F_w^\times$ scales $\nu_w$ by the normalized absolute value $|a|_w$. The measures $\mu_w$ are the archimedean factors of the Tamagawa measure $\mu=\bigotimes_v\mu_v$ of the idele group (Lemma A.3.2.4).
--
--   **Formalization Note.** $F_w^\times$ is the unit group of `w.Completion` with its Borel $\sigma$-algebra; $|x|_w$ is `‖x‖ ^ w.mult`. `IsHaarMeasure` is Mathlib's notion: left-invariant, finite on compacts, positive on non-empty open sets.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 560, Definition A.3.2.2(1)

import Mathlib
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

namespace MasulloGRH

theorem infiniteLocalMulTamagawa_isHaarMeasure
    (F : Type*) [Field F] [NumberField F] (w : InfinitePlace F) :
    (infiniteLocalMulTamagawa F w).IsHaarMeasure := by sorry

end MasulloGRH
