-- Prove2me | Theorems.Thm_IsAdicComplete_of_isNilpotent
-- name    : IsAdicComplete.of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/fb976745-7f7a-532a-81ac-110bad13199a
-- title:
--   Nilpotent ideals are adically complete
-- statement:
--   Let $R$ be a commutative ring and $I \subseteq R$ an ideal which is nilpotent, i.e. $I^N = 0$ for some natural number $N$. The assertion is that $R$, viewed as a module over itself, is $I$-adically complete in Mathlib's sense: `IsAdicComplete I R` combines the Hausdorff property, that an element $x \in R$ with $x \equiv 0$ modulo $I^n \cdot R$ for every $n$ is zero (so $\bigcap_n I^n = 0$), with precompleteness, that for every family $(f_n)_{n \in \mathbb{N}}$ of elements of $R$ satisfying $f_m \equiv f_n \pmod{I^n \cdot R}$ whenever $n \le m$ there exists $L \in R$ with $L \equiv f_n \pmod{I^n \cdot R}$ for all $n$. Equivalently, the natural map $R \to \varprojlim_n R/I^n$ is bijective. No local, Noetherian or finiteness hypotheses are imposed on $R$.
--
--   This fills the gap between Mathlib's existing adic-completeness instances (for the zero ideal and for subsingleton modules) and the case needed in deformation theory, where the objects considered are Artinian local rings whose maximal ideal is nilpotent; combined with Mathlib's Newton-iteration result that $I$-adically complete rings are Henselian, it yields Henselianity of such rings. It is used in the formalisation of hulls and deformation functors, in the construction of Drinfeld-type bases for formal groups, and in the analysis of adic completions of rings arising from modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAdicComplete_of_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsAdicComplete.of_isNilpotent {R : Type u} [CommRing R] {I : Ideal R} (hI : IsNilpotent I) :
    IsAdicComplete I R := by sorry
