-- Prove2me | Theorems.Thm_GenericGroupWE_Main_lemma_6_2
-- name    : GenericGroupWE.Main.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:04.379654+00:00
-- url     : https://prove2.me/theorems/15d75606-2488-4b4f-b287-ed30b65764c3
-- title:
--   Lemma 6.2 — Rectangular Boolean tables
-- statement:
--   Let $q_s$ be quadratic polynomials in $N$ variables with no common Boolean zero. Let $a,b\ge0$ and let $L$ be a linear functional on polynomials through degree $a+b$. If $a,b>0$, assume $L((x_i^2-x_i)f)=L(q_sf)=0$ whenever $\deg f+2\le a+b$. With rows and columns indexed by all ordinary monomials of degrees at most $a$ and $b$, including $1$, respectively,
--
--   $$H_{a,b}(L)\ne0\Longrightarrow \operatorname{rank}H_{a,b}(L)\ge\binom{a+b}{a}.$$
--
--   Neither family of identities is required when $a=0$ or $b=0$. The rank is algebraic; no positive-functional or probability assumption occurs.
--
--   Differences from the source:
--   - generalization: the prime field used throughout the paper → any field; reason: the selector and rank arguments use field operations only and specialize to every prime field
--   - encoding: a functional on the degree-truncated polynomial space → a total linear functional whose values above degree a+b are unused; reason: every truncated functional extends to the polynomial space by assigning arbitrary values to the other monomials
--   - encoding: finite indexed families and field residues → Fin-indexed families and ZMod prime fields; reason: zero-based indices and explicit finite carriers change no mathematical instance
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, Lemma 6.2, PDF p. 25 (printed p. 24).

import Definitions.Def_GenericGroupWE_Main_Tables

namespace GenericGroupWE.Main

theorem lemma_6_2 (K : Type*) [Field K] (N k a b : ℕ)
    (q : Fin k → MvPolynomial (Fin N) K) (hq : ∀ s, (q s).totalDegree ≤ 2)
    (hunsat : NoBooleanZero q) (L : MvPolynomial (Fin N) K →ₗ[K] K)
    (hidentities : a ≠ 0 → b ≠ 0 → AnnihilatesEquations q L (a+b))
    (hne : rectangularTable a b L ≠ 0) :
    Nat.choose (a+b) a ≤ (rectangularTable a b L).rank := by sorry

end GenericGroupWE.Main
