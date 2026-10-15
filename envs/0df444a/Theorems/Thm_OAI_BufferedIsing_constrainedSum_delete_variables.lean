-- Prove2me | Theorems.Thm_OAI_BufferedIsing_constrainedSum_delete_variables
-- name    : OAI.BufferedIsing.constrainedSum_delete_variables
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:12:23.049346+00:00
-- url     : https://prove2.me/theorems/04649e5f-0221-4c35-87dd-31b04fe3ef10
-- title:
--   Sums with pinned spins are sums over the free spins of the pin extension
-- statement:
--   Let $G$ be a finite graph on $V=\{0,\dots,n-1\}$ whose edges $e$ have endpoints $l(e)\neq r(e)$ and couplings $K_e\ge0$, let $h\in\mathbb{R}^V$ be a field and $w_h(\sigma)=\exp\bigl(\sum_eK_e\sigma_{l(e)}\sigma_{r(e)}+\sum_vh_v\sigma_v\bigr)$ the Ising weight. Let $F\subseteq V$, let $\tau\in\{-1,+1\}^V$, and let $P$ be any property of configurations. For $\eta\in\{-1,+1\}^{V\setminus F}$ write $\tau_F\oplus\eta$ for the configuration equal to $\tau$ on $F$ and to $\eta$ on $V\setminus F$. Then
--
--   $$\sum_{\sigma\in\{-1,+1\}^V:\ \sigma_F=\tau_F,\ P(\sigma)}w_h(\sigma)=\sum_{\eta\in\{-1,+1\}^{V\setminus F}}\mathbf{1}\bigl[P(\tau_F\oplus\eta)\bigr]\,w_h(\tau_F\oplus\eta).$$
--
--   The identity says that pinning the spins on $F$ is the same as eliminating those variables: the constrained sum becomes an unconstrained sum over the free spins, while the weight is still evaluated on the full configuration and therefore keeps every interaction between $F$ and the remaining sites. It is used to rewrite pinned marginals as weights of a model on $V\setminus F$.
--
--   **Formalization Note** The left side is `constrainedSum G h (fun σ => AgreesOn F σ τ ∧ P σ)`, and the right side sums over functions `KeptVertex F → Bool` on the subtype of vertices outside $F$, extended by `pinExtension F τ`. The predicate $P$ is arbitrary (decidability is classical).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/SpinCorrelation.lean#L40-L60

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.constrainedSum_delete_variables {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (P : Spins n → Prop) :
    constrainedSum G h (fun σ => AgreesOn F σ τ ∧ P σ) =
      ∑ σ : KeptVertex F → Bool,
        if P (pinExtension F τ σ) then weight G h (pinExtension F τ σ) else 0 := by sorry
