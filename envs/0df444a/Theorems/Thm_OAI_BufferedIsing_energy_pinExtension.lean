-- Prove2me | Theorems.Thm_OAI_BufferedIsing_energy_pinExtension
-- name    : OAI.BufferedIsing.energy_pinExtension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:18:08.860857+00:00
-- url     : https://prove2.me/theorems/cdb048ee-d589-49e0-ab1d-bb057759e492
-- title:
--   Exact elimination of pinned spins: constant, deleted-graph energy and induced boundary fields
-- statement:
--   Let $G$ be a finite graph on the vertex set $V=\{0,\dots,n-1\}$ with separately indexed edges $e$ (parallel edges allowed), endpoints $\ell(e)\neq r(e)$ and couplings $K_e\ge0$, let $h\in\mathbb{R}^V$ be an external field and $\mathcal H_h(\rho)=\sum_eK_e\rho_{\ell(e)}\rho_{r(e)}+\sum_{v\in V}h_v\rho_v$ the Ising energy. Fix $F\subseteq V$ and $\tau\in\{-1,+1\}^V$, and let
--   $$
--   C_F(\tau)=\sum_{\ell(e),r(e)\in F}K_e\tau_{\ell(e)}\tau_{r(e)}+\sum_{v\in F}h_v\tau_v,\qquad h^{F,\tau}_v=h_v+\sum_{\ell(e)=v,\ r(e)\in F}K_e\tau_{r(e)}+\sum_{r(e)=v,\ \ell(e)\in F}K_e\tau_{\ell(e)}
--   $$
--   be the pin constant and, for $v\notin F$, the field induced by the pinned spins. Let $E_F=\{e:\ \ell(e)\notin F,\ r(e)\notin F\}$ be the edges that survive deletion of $F$. For a configuration $\sigma\in\{-1,+1\}^{V\setminus F}$ of the free vertices write $\mathcal H^{\mathrm{del}}_F(\sigma)=\sum_{e\in E_F}K_e\sigma_{\ell(e)}\sigma_{r(e)}$ for its zero-field energy on the vertex-deleted graph, and $\sigma^{\tau}$ for the configuration on $V$ equal to $\tau$ on $F$ and to $\sigma$ on $V\setminus F$.
--
--   **Theorem.** For every $\sigma\in\{-1,+1\}^{V\setminus F}$,
--   $$
--   \mathcal H_h(\sigma^{\tau})=C_F(\tau)+\mathcal H^{\mathrm{del}}_F(\sigma)+\sum_{v\in V\setminus F}h^{F,\tau}_v\,\sigma_v .
--   $$
--
--   Consequently $e^{\mathcal H_h(\sigma^\tau)}=e^{C_F(\tau)}\exp\big(\mathcal H^{\mathrm{del}}_F(\sigma)+\sum_{v\notin F}h^{F,\tau}_v\sigma_v\big)$: the Ising model with the spins on $F$ fixed to $\tau$ is, up to a constant factor that cancels from every normalized quantity, an Ising model on the graph with $F$ deleted, in which each edge from a free vertex to $F$ has been replaced by a finite real field on its free endpoint. These induced fields come from the actual pinned spins and may have either sign; nothing is replaced by mere deletion.
--
--   **Formalization Note** $\sigma^\tau$ is `pinExtension F τ σ`, free configurations are `KeptVertex F → Bool`, the induced field is `pinField G h F τ v`, the constant is `pinConstant G h F τ`, and $\mathcal H^{\mathrm{del}}_F$ is `deletedEnergy G F σ`. The latter evaluates $\sigma$ through `extendKept`, which pads with `false` on $F$; the padding is never used because the edges in $E_F$ avoid $F$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/PinnedMarginal.lean#L225-L251

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

theorem OAI.BufferedIsing.energy_pinExtension {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (σ : KeptVertex F → Bool) :
    energy G h (pinExtension F τ σ) = pinConstant G h F τ +
      deletedEnergy G F σ + ∑ v : KeptVertex F, pinField G h F τ v * spin (σ v) := by sorry
