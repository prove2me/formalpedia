-- Prove2me | Theorems.Thm_HaagerupReduction_Dyadic_lemma_2_7
-- name    : HaagerupReduction.Dyadic.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:40.811244+00:00
-- url     : https://prove2.me/theorems/b32101d9-4eec-418b-8a48-b1060a075585
-- title:
--   Lemma 2.7, p. 11 — Φ_n(x) → x σ-strongly for x ∈ R; hence ⋃_{n≥1} R_n is σ-strongly dense in R
-- statement:
--   Let $\mathcal R = M\rtimes_{\sigma^\varphi}G$, $\hat\varphi$ and $\mathcal R_n = \mathcal R_{\varphi_n}$ be as in the model, let $\hat S$ be modular data of $(\mathcal R,\hat\varphi)$ ($\hat S.M = \mathcal R$, $\hat S.\xi = \hat\xi$), and for each $n\ge1$ let $\Phi_n$ be a normal faithful conditional expectation from $\mathcal R$ onto $\mathcal R_n$ with $\hat\varphi\circ\Phi_n = \hat\varphi$ and $\sigma^{\hat\varphi}_t\circ\Phi_n = \Phi_n\circ\sigma^{\hat\varphi}_t$ (the expectations of Lemma 2.4 (ii)). Then:
--
--   1. for every $x\in\mathcal R$, $\Phi_n(x)\to x$ strongly: $\Phi_n(x)h\to xh$ for every $h\in\ell^2(G,H)$;
--   2. consequently every $x\in\mathcal R$ is the strong limit of a sequence in $\bigcup_{n\ge1}\mathcal R_n$.
--
--   This is the density statement (ii) of Theorem 2.1.
--
--   **Formalization Note.** The paper says σ-strongly. The sequence $(\Phi_n(x))$ is bounded by $\|x\|$, and on bounded sets the σ-strong and strong topologies agree, so strong convergence is the same statement; likewise a strongly convergent sequence is bounded, so part 2 gives σ-strong density. The modular data $\hat S$ are a hypothesis (existence: `dual_modular_data_exists`).
-- source:
--   Haagerup, Junge & Xu, A reduction method for noncommutative Lp-spaces and applications, arXiv:0806.3635v2, p. 11, Lemma 2.7

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HaagerupReduction_Dyadic_Model

namespace HaagerupReduction.Dyadic

universe u

open OAI.BoundedRecovery
open Filter Topology

/-- Lemma 2.7: `Φ_n(x) → x` strongly for `x ∈ R`; consequently `⋃_{n ≥ 1} R_n` is
(sequentially) strongly dense in `R`. -/
theorem lemma_2_7 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : StandardModularData H)
    (Sh : StandardModularData (L2G H)) (hM : Sh.M = crossedProduct S) (hxi : Sh.xi = xiHat S)
    (Φ : ℕ → (L2G H →L[ℂ] L2G H) → (L2G H →L[ℂ] L2G H))
    (hΦ : ∀ n : ℕ, 1 ≤ n → IsInvariantCondExp S Sh (Rn S n) (Φ n)) :
    (∀ x ∈ crossedProduct S, ∀ h : L2G H, Tendsto (fun n : ℕ => Φ n x h) atTop (𝓝 (x h))) ∧
    ∀ x ∈ crossedProduct S, ∃ y : ℕ → (L2G H →L[ℂ] L2G H),
      (∀ k, y k ∈ ⋃ n ≥ 1, Rn S n) ∧ ∀ h : L2G H, Tendsto (fun k : ℕ => y k h) atTop (𝓝 (x h)) := by sorry

end HaagerupReduction.Dyadic
