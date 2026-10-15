-- Prove2me | Theorems.Thm_OAI_BufferedIsing_energy_pin_expansion
-- name    : OAI.BufferedIsing.energy_pin_expansion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:17:47.591998+00:00
-- url     : https://prove2.me/theorems/c75ea134-d068-4534-8e42-3a3f71a4a637
-- title:
--   Energy expansion of an Ising configuration that agrees with pinned spins on a vertex set
-- statement:
--   Let $G$ be a finite graph on the vertex set $V=\{0,\dots,n-1\}$ with separately indexed edges $e$ (parallel edges allowed), endpoints $\ell(e)\neq r(e)$ and couplings $K_e\ge0$, let $h\in\mathbb{R}^V$ be an external field, and let $\mathcal H_h(\rho)=\sum_eK_e\rho_{\ell(e)}\rho_{r(e)}+\sum_{v\in V}h_v\rho_v$ be the Ising energy of $\rho\in\{-1,+1\}^V$. Fix a vertex set $F\subseteq V$ and a configuration $\tau\in\{-1,+1\}^V$. Define the *pin constant*
--   $$
--   C_F(\tau)=\sum_{e:\ \ell(e)\in F,\ r(e)\in F}K_e\,\tau_{\ell(e)}\tau_{r(e)}+\sum_{v\in F}h_v\tau_v
--   $$
--   and, for $v\notin F$, the *induced field*
--   $$
--   h^{F,\tau}_v=h_v+\sum_{e:\ \ell(e)=v,\ r(e)\in F}K_e\,\tau_{r(e)}+\sum_{e:\ r(e)=v,\ \ell(e)\in F}K_e\,\tau_{\ell(e)} .
--   $$
--
--   **Theorem.** If $\rho\in\{-1,+1\}^V$ agrees with $\tau$ on $F$, that is $\rho_v=\tau_v$ for all $v\in F$, then
--   $$
--   \mathcal H_h(\rho)=C_F(\tau)+\sum_{e:\ \ell(e)\notin F,\ r(e)\notin F}K_e\,\rho_{\ell(e)}\rho_{r(e)}+\sum_{v\in V\setminus F}h^{F,\tau}_v\,\rho_v .
--   $$
--
--   Thus, once the spins on $F$ are fixed, the energy splits into a constant that depends only on the pinned spins, the interaction along edges with both endpoints free, and a linear term in which every edge from a free vertex $v$ to $F$ acts as an extra field $K_e\tau$ on $v$. The identity is exact and uses no sign information; the induced fields may well be negative. It is the algebraic core of the fact that pinning a set of sites is the same as deleting it and adding boundary fields.
--
--   **Formalization Note** Spins are Booleans read as $\pm1$ via `spin`. $C_F(\tau)$ is `pinConstant G h F τ`. Conditional sums over edges are written as sums over all edges of `if … then … else 0`, and the last sum runs over all of `Fin n` with summand $0$ on $F$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/PinnedMarginal.lean#L159-L216

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.energy_pin_expansion {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ ρ : Spins n) (hρ : AgreesOn F ρ τ) :
    energy G h ρ = pinConstant G h F τ +
      (∑ e, if G.left e ∉ F ∧ G.right e ∉ F then
        G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e)) else 0) +
      ∑ v : Fin n, if v ∉ F then
        (h v + (∑ e, if G.left e = v ∧ G.right e ∈ F then
          G.coupling e * spin (τ (G.right e)) else 0) +
          ∑ e, if G.right e = v ∧ G.left e ∈ F then
            G.coupling e * spin (τ (G.left e)) else 0) * spin (ρ v) else 0 := by sorry
