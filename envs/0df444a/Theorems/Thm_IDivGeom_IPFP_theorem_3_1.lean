-- Prove2me | Theorems.Thm_IDivGeom_IPFP_theorem_3_1
-- name    : IDivGeom.IPFP.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:06:11.030196+00:00
-- url     : https://prove2.me/theorems/c2386845-f1f3-403a-9848-35fab5176da1
-- title:
--   Theorem 3.1 — form of the R-density of the I-projection under arbitrary linear constraints
-- statement:
--   Let $\{f_\gamma\}_{\gamma\in\Gamma}$ be an arbitrary family of real-valued $\mathcal X$-measurable functions on $X$ and $\{a_\gamma\}_{\gamma\in\Gamma}$ real constants. Let $\mathcal E$ be the set of all probability distributions $P$ on $(X,\mathcal X)$ for which every integral $\int f_\gamma\,dP$ exists and equals $a_\gamma$. Let $R$ be a probability distribution.
--
--   1. If $R$ has I-projection $Q$ on $\mathcal E$, then its $R$-density has the form
--   $$
--   q_R(x)=\begin{cases}c\,\exp g(x), & x\notin N,\\ 0, & x\in N,\end{cases}\qquad(3.4)
--   $$
--   where $N$ is a measurable set with $P(N)=0$ for every $P\in\mathcal E$ with $I(P\|R)<\infty$, and $g$ belongs to the closed linear subspace of $L_1(Q)$ spanned by the $f_\gamma$'s.
--   2. Conversely, if $Q\in\mathcal E$ has an $R$-density of the form (3.4), with such an $N$, where $g$ is a finite linear combination of the $f_\gamma$'s (no closure), then $Q$ is the I-projection of $R$ on $\mathcal E$ and
--   $$
--   I(P\|R)=I(P\|Q)+I(Q\|R)\quad\text{for all }P\in\mathcal E.\qquad(3.1)
--   $$
--
--   The paper's Example (3.5)–(3.8) shows that neither condition is both necessary and sufficient in general; Corollary 3.1 closes the gap for finitely many constraints.
--
--   **Formalization Note** "The integral exists" is integrability of $f_\gamma$ (so a non-integrable $f_\gamma$ cannot satisfy a constraint through a default value). Membership of $g$ in the closed span is stated in Lean's $L^1(Q)$: $g$ and every $f_\gamma$ are $Q$-integrable, and the class of $g$ lies in the topological closure of the span of the classes of the $f_\gamma$. The density equation holds $R$-almost everywhere; in part 2, "$Q$ has an $R$-density" is written as $Q\ll R$. A finite linear combination is $\sum_{\gamma\in s}w_\gamma f_\gamma$ over a finite set $s\subseteq\Gamma$.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 152, Theorem 3.1 (PDF p. 7)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory

namespace IDivGeom.IPFP
attribute [local instance] Classical.propDecidable

theorem theorem_3_1 {X : Type*} [MeasurableSpace X]
    {Γ : Type*} (f : Γ → X → ℝ) (hf : ∀ γ, Measurable (f γ)) (a : Γ → ℝ)
    (R : Measure X) [IsProbabilityMeasure R] :
    (∀ Q, IsIProjection R (momentSet f a) Q →
      ∃ (c : ℝ) (N : Set X) (g : X → ℝ),
        MeasurableSet N ∧
        (∀ P ∈ momentSet f a, klDiv P R ≠ ⊤ → P N = 0) ∧
        InClosedL1Span Q f g ∧
        ∀ᵐ x ∂ R, (Q.rnDeriv R x).toReal =
          if x ∈ N then 0 else c * Real.exp (g x)) ∧
    (∀ Q ∈ momentSet f a,
      (Q ≪ R ∧ ∃ (c : ℝ) (N : Set X) (s : Finset Γ) (w : Γ → ℝ),
        MeasurableSet N ∧
        (∀ P ∈ momentSet f a, klDiv P R ≠ ⊤ → P N = 0) ∧
        ∀ᵐ x ∂ R, (Q.rnDeriv R x).toReal =
          if x ∈ N then 0 else c * Real.exp (∑ γ ∈ s, w γ * f γ x)) →
      IsIProjection R (momentSet f a) Q ∧
        ∀ P ∈ momentSet f a, klDiv P R = klDiv P Q + klDiv Q R) := by sorry

end IDivGeom.IPFP
