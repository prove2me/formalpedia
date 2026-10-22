-- Prove2me | Theorems.Thm_HaagerupReduction_Dyadic_lemma_2_4_ii_iii
-- name    : HaagerupReduction.Dyadic.lemma_2_4_ii_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:14.822479+00:00
-- url     : https://prove2.me/theorems/f8eaaf56-5d53-4049-9c24-7848d8227265
-- title:
--   Lemma 2.4 (ii)–(iii), p. 8 — unique φ̂-preserving σ^φ̂-commuting normal faithful conditional expectation Φ_n of R onto R_n = R_{ϕ_n}; R_n ⊂ R_{n+1}
-- statement:
--   Let $\mathcal R = M\rtimes_{\sigma^\varphi}G$, $\hat\varphi$ and $\varphi_n(x) = \hat\varphi(e^{-a_n}x)$ be as in the model, let $\hat S$ be modular data of $(\mathcal R,\hat\varphi)$ ($\hat S.M = \mathcal R$, $\hat S.\xi = \hat\xi$) with modular group $\sigma^{\hat\varphi}$, and let $\mathcal R_n = \mathcal R_{\varphi_n} = \{x\in\mathcal R: \varphi_n(xy) = \varphi_n(yx)\ \forall y\in\mathcal R\}$. For every $n\ge1$:
--
--   1. there exists a normal faithful conditional expectation $\Phi_n$ from $\mathcal R$ onto $\mathcal R_n$ such that
--   $$\hat\varphi\circ\Phi_n = \hat\varphi \quad\text{and}\quad \sigma^{\hat\varphi}_t\circ\Phi_n = \Phi_n\circ\sigma^{\hat\varphi}_t,\qquad t\in\mathbb R;$$
--   2. it is unique: any two such maps agree on $\mathcal R$;
--   3. $\mathcal R_n\subseteq\mathcal R_{n+1}$.
--
--   These expectations are the $\Phi_n$ of Theorem 2.1 (iii), and part 3 is the monotonicity of the sequence $(\mathcal R_n)$.
--
--   **Formalization Note.** The modular data $\hat S$ are a hypothesis (existence: `dual_modular_data_exists`). Maps are defined on all bounded operators of $\ell^2(G,H)$ but only their values on $\mathcal R$ are constrained, so uniqueness is stated on $\mathcal R$. "Normal faithful conditional expectation" is unfolded in the model (into, identity on $\mathcal R_n$, linear, positive, bimodular, faithful, normal).
-- source:
--   Haagerup, Junge & Xu, A reduction method for noncommutative Lp-spaces and applications, arXiv:0806.3635v2, p. 8, Lemma 2.4 (ii) and (iii)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HaagerupReduction_Dyadic_Model

namespace HaagerupReduction.Dyadic

universe u

open OAI.BoundedRecovery
open Filter Topology

/-- Lemma 2.4 (ii), (iii): for `n ≥ 1` there is a unique normal faithful conditional expectation
`Φ_n` from `R` onto `R_n = R_{ϕ_n}` with `φ̂ ∘ Φ_n = φ̂` and `σ^φ̂_t ∘ Φ_n = Φ_n ∘ σ^φ̂_t`; and
`R_n ⊆ R_{n+1}`. -/
theorem lemma_2_4_ii_iii {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H)
    (Sh : StandardModularData (L2G H)) (hM : Sh.M = crossedProduct S) (hxi : Sh.xi = xiHat S) (n : ℕ) (hn : 1 ≤ n) :
    (∃ Φ : (L2G H →L[ℂ] L2G H) → (L2G H →L[ℂ] L2G H), IsInvariantCondExp S Sh (Rn S n) Φ) ∧
    (∀ Φ Ψ : (L2G H →L[ℂ] L2G H) → (L2G H →L[ℂ] L2G H),
      IsInvariantCondExp S Sh (Rn S n) Φ → IsInvariantCondExp S Sh (Rn S n) Ψ →
      ∀ x ∈ crossedProduct S, Φ x = Ψ x) ∧
    Rn S n ⊆ Rn S (n + 1) := by sorry

end HaagerupReduction.Dyadic
