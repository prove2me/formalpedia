-- Prove2me | Theorems.Thm_InconsistentDR_Shadow_lemma_3_2
-- name    : InconsistentDR.Shadow.lemma_3_2
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T00:10:43.165024+00:00
-- url     : https://prove2.me/theorems/503bacec-7b07-449e-bdae-18e276d2c70d
-- title:
--   Lemma 3.2, p. 9 — polar of the recession cone of $\overline{\operatorname{dom}}A$ recedes in $\overline{\operatorname{ran}}A$, and vice versa
-- statement:
--   Let $X$ be a real Hilbert space and let $A:X\rightrightarrows X$ be a maximally monotone operator with resolvent $J_A=(\mathrm{Id}+A)^{-1}$. For a closed set $C\subseteq X$ write
--   $$\operatorname{rec}C=\{d\in X:\ c+td\in C\ \text{ for all } c\in C,\ t\ge0\}$$
--   for its recession cone, and $K^{\ominus}=\{u:\langle d,u\rangle\le0\ \text{for all } d\in K\}$ for the polar cone of a set $K$. Then:
--
--   1. $\big(\operatorname{rec}\overline{\operatorname{dom}}\,A\big)^{\ominus}\subseteq\operatorname{rec}\overline{\operatorname{ran}}\,A$;
--   2. $\big(\operatorname{rec}\overline{\operatorname{ran}}\,A\big)^{\ominus}\subseteq\operatorname{rec}\overline{\operatorname{dom}}\,A$.
--
--   This is Lemma 3.2 of the paper (stated there for both operators $A$ and $B$ of the pair; it is a statement about one operator at a time). In the paper it follows from the Brezis–Haraux theorem and Zarantonello's identity $\overline{\operatorname{ran}}\,N_{C}=(\operatorname{rec}C)^{\ominus}$. It locates the vectors $v_D$ and $v_R$ in Proposition 3.3(ii) and (iv), and from these the orthogonality $\langle v_D,v_R\rangle=0$ and the decomposition $v=v_D+v_R$ follow.
--
--   **Formalization Note** $A$ is given with the published `IsMaximalMonotone` and a resolvent map `J` with `IsResolvent 1 A J`; `dom` and `ran` are the published operator domain and range. The recession cone and the polar cone are written out explicitly as above, for the closures of the domain and the range.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (2021), p. 9, Lemma 3.2

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

namespace InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence

/-- Lemma 3.2, p. 9, for one maximally monotone operator `A` (with resolvent `J`), with the
recession cone `rec C = {d | ∀ c ∈ C, ∀ t ≥ 0, c + t d ∈ C}` and the polar cone
`K^⊖ = {u | ∀ d ∈ K, ⟪d, u⟫ ≤ 0}` written out:
(i) `(rec cl dom A)^⊖ ⊆ rec cl ran A`; (ii) `(rec cl ran A)^⊖ ⊆ rec cl dom A`. -/
theorem lemma_3_2 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A : X → Set X) (hA : IsMaximalMonotone A) (J : X → X) (hJ : IsResolvent 1 A J) :
    (∀ u : X, (∀ d : X, (∀ c ∈ closure (dom A), ∀ t : ℝ, 0 ≤ t → c + t • d ∈ closure (dom A)) →
        ⟪d, u⟫_ℝ ≤ 0) →
      ∀ r ∈ closure (ran A), ∀ t : ℝ, 0 ≤ t → r + t • u ∈ closure (ran A)) ∧
    (∀ u : X, (∀ d : X, (∀ c ∈ closure (ran A), ∀ t : ℝ, 0 ≤ t → c + t • d ∈ closure (ran A)) →
        ⟪d, u⟫_ℝ ≤ 0) →
      ∀ r ∈ closure (dom A), ∀ t : ℝ, 0 ≤ t → r + t • u ∈ closure (dom A)) := by sorry

end InconsistentDR.Shadow
